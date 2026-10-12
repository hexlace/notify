//! Watcher implementation for Darwin's FSEvents API
//!
//! The FSEvents API provides a mechanism to notify clients about directories they ought to re-scan
//! in order to keep their internal data structures up-to-date with respect to the true state of
//! the file system. (For example, when files or directories are created, modified, or removed.) It
//! sends these notifications "in bulk", possibly notifying the client of changes to several
//! directories in a single callback.
//!
//! For more information see the [FSEvents API reference][ref].
//!
//! TODO: document event translation
//!
//! [ref]: https://developer.apple.com/library/mac/documentation/Darwin/Reference/FSEvents_Ref/

#![allow(non_upper_case_globals, dead_code)]

use crate::event::*;
use crate::{
    unbounded, Config, Error, EventHandler, PathsMut, RecursiveMode, Result, Sender, Watcher,
};
use fsevent_sys as fs;
use fsevent_sys::core_foundation as cf;
use std::collections::HashMap;
use std::ffi::CStr;
use std::fmt;
use std::os::raw;
use std::path::{Path, PathBuf};
use std::ptr;
use std::sync::{Arc, Mutex};
use std::thread;

bitflags::bitflags! {
  #[repr(C)]
  #[derive(Debug)]
  struct StreamFlags: u32 {
    const NONE = fs::kFSEventStreamEventFlagNone;
    const MUST_SCAN_SUBDIRS = fs::kFSEventStreamEventFlagMustScanSubDirs;
    const USER_DROPPED = fs::kFSEventStreamEventFlagUserDropped;
    const KERNEL_DROPPED = fs::kFSEventStreamEventFlagKernelDropped;
    const IDS_WRAPPED = fs::kFSEventStreamEventFlagEventIdsWrapped;
    const HISTORY_DONE = fs::kFSEventStreamEventFlagHistoryDone;
    const ROOT_CHANGED = fs::kFSEventStreamEventFlagRootChanged;
    const MOUNT = fs::kFSEventStreamEventFlagMount;
    const UNMOUNT = fs::kFSEventStreamEventFlagUnmount;
    const ITEM_CREATED = fs::kFSEventStreamEventFlagItemCreated;
    const ITEM_REMOVED = fs::kFSEventStreamEventFlagItemRemoved;
    const INODE_META_MOD = fs::kFSEventStreamEventFlagItemInodeMetaMod;
    const ITEM_RENAMED = fs::kFSEventStreamEventFlagItemRenamed;
    const ITEM_MODIFIED = fs::kFSEventStreamEventFlagItemModified;
    const FINDER_INFO_MOD = fs::kFSEventStreamEventFlagItemFinderInfoMod;
    const ITEM_CHANGE_OWNER = fs::kFSEventStreamEventFlagItemChangeOwner;
    const ITEM_XATTR_MOD = fs::kFSEventStreamEventFlagItemXattrMod;
    const IS_FILE = fs::kFSEventStreamEventFlagItemIsFile;
    const IS_DIR = fs::kFSEventStreamEventFlagItemIsDir;
    const IS_SYMLINK = fs::kFSEventStreamEventFlagItemIsSymlink;
    const OWN_EVENT = fs::kFSEventStreamEventFlagOwnEvent;
    const IS_HARDLINK = fs::kFSEventStreamEventFlagItemIsHardlink;
    const IS_LAST_HARDLINK = fs::kFSEventStreamEventFlagItemIsLastHardlink;
    const ITEM_CLONED = fs::kFSEventStreamEventFlagItemCloned;
  }
}

/// FSEvents-based `Watcher` implementation
pub struct FsEventWatcher {
    paths: cf::CFMutableArrayRef,
    since_when: fs::FSEventStreamEventId,
    latency: cf::CFTimeInterval,
    flags: fs::FSEventStreamCreateFlags,
    event_handler: Arc<Mutex<dyn EventHandler>>,
    runloop: Option<(cf::CFRunLoopRef, thread::JoinHandle<()>)>,
    recursive_info: HashMap<PathBuf, bool>,
}

impl fmt::Debug for FsEventWatcher {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_struct("FsEventWatcher")
            .field("paths", &self.paths)
            .field("since_when", &self.since_when)
            .field("latency", &self.latency)
            .field("flags", &self.flags)
            .field("event_handler", &Arc::as_ptr(&self.event_handler))
            .field("runloop", &self.runloop)
            .field("recursive_info", &self.recursive_info)
            .finish()
    }
}

// CFMutableArrayRef is a type alias to *mut libc::c_void, so FsEventWatcher is not Send/Sync
// automatically. It's Send because the pointer is not used in other threads.
unsafe impl Send for FsEventWatcher {}

// It's Sync because all methods that change the mutable state use `&mut self`.
unsafe impl Sync for FsEventWatcher {}

/// The flags with which FSEvents says that events a stream would have
/// reported were lost, coalesced or can no longer be told apart, so that a
/// handler must look at the file system again instead of trusting what it
/// was told. Each reaches the handler as a rescan (`translate_flags`).
///
/// - `MUST_SCAN_SUBDIRS` (`kFSEventStreamEventFlagMustScanSubDirs`): events
///   below the event's path were coalesced or dropped, and that subtree must
///   be scanned again.
/// - `USER_DROPPED` (`kFSEventStreamEventFlagUserDropped`): events were
///   dropped in user space, before they reached this stream's client.
/// - `KERNEL_DROPPED` (`kFSEventStreamEventFlagKernelDropped`): the kernel's
///   queue overflowed and events were dropped before `fseventsd` saw them.
/// - `IDS_WRAPPED` (`kFSEventStreamEventFlagEventIdsWrapped`): the event id
///   counter wrapped, so ids issued before it no longer order against those
///   issued after.
/// - `ROOT_CHANGED` (`kFSEventStreamEventFlagRootChanged`): a watched path or
///   one of its ancestors was moved, removed or replaced, so the path no
///   longer names what was watched.
const LOSS_NOTICES: StreamFlags = StreamFlags::MUST_SCAN_SUBDIRS
    .union(StreamFlags::USER_DROPPED)
    .union(StreamFlags::KERNEL_DROPPED)
    .union(StreamFlags::IDS_WRAPPED)
    .union(StreamFlags::ROOT_CHANGED);

/// The loss notices that say something about the whole stream rather than
/// one subtree: a drop or a wrap loses events wherever they were. FSEvents
/// reports a drop once for each path the stream watches, at that path (its
/// header says so, and a user drop provoked on macOS 26.5 arrived that way),
/// and documents no path for a wrap, so neither is filtered by its path.
const STREAM_LOSS_NOTICES: StreamFlags = StreamFlags::USER_DROPPED
    .union(StreamFlags::KERNEL_DROPPED)
    .union(StreamFlags::IDS_WRAPPED);

/// What of an event FSEvents delivered is handed to the event handler.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Forwarding {
    /// Every event the flags translate to: the event's path is watched.
    All,
    /// Only the rescan: a loss notice at a path nothing watches. Any
    /// ordinary flags it carries describe a path the handler was never
    /// asked about, which the path filter would have dropped.
    RescanOnly,
    /// Nothing: the event says nothing about any watch.
    Nothing,
}

/// Decides what of an event FSEvents delivered at `path` with `flags` is
/// handed to the event handler, against the watches in `recursive_info`.
///
/// An event whose path is watched ([`is_watched`]) is handed on whole. A
/// notice that the stream's history was lost ([`LOSS_NOTICES`]) is never
/// decided by its path alone, because FSEvents puts it on whatever path it
/// chooses, which need not be one that was watched. A drop or a wrap
/// ([`STREAM_LOSS_NOTICES`]) always hands on its rescan. A notice about a
/// subtree hands on its rescan when a watch lies at or below its path (`/`,
/// a volume's root, any ancestor of a watch). A notice at an unwatched path
/// hands on its rescan alone, and the ordinary flags beside it are dropped
/// as any event at that path would be. A notice that touches no watch, and
/// every ordinary event at an unwatched path, hands on nothing: it lies
/// wholly in a part of the tree no watch reports, and stands only for
/// events the handler would not have been given anyway.
fn forwarding(
    recursive_info: &HashMap<PathBuf, bool>,
    path: &Path,
    flags: &StreamFlags,
) -> Forwarding {
    if is_watched(recursive_info, path) {
        return Forwarding::All;
    }
    let lost = flags.intersects(STREAM_LOSS_NOTICES)
        || (flags.intersects(LOSS_NOTICES) && has_a_watch_at_or_below(recursive_info, path));
    if lost {
        Forwarding::RescanOnly
    } else {
        Forwarding::Nothing
    }
}

/// Whether some watched path in `recursive_info` is `path` or lies below it.
///
/// Scans every watch, unlike [`is_watched`], because "is anything below
/// this" is not a lookup in a map keyed by path; it runs only for a loss
/// notice that [`is_watched`] did not already settle, which is rare.
fn has_a_watch_at_or_below(recursive_info: &HashMap<PathBuf, bool>, path: &Path) -> bool {
    recursive_info
        .keys()
        .any(|watched| watched.starts_with(path))
}

fn translate_flags(flags: StreamFlags, precise: bool) -> Vec<Event> {
    let mut evs = Vec::new();

    // «Denotes a sentinel event sent to mark the end of the "historical" events
    // sent as a result of specifying a `sinceWhen` value in the FSEvents.Create
    // call that created this event stream. After invoking the client's callback
    // with all the "historical" events that occurred before now, the client's
    // callback will be invoked with an event where the HistoryDone flag is set.
    // The client should ignore the path supplied in this callback.»
    // — https://www.mbsplugins.eu/FSEventsNextEvent.shtml
    //
    // As a result, we just stop processing here and return an empty vec, which
    // will ignore this completely and not emit any Events whatsoever.
    if flags.contains(StreamFlags::HISTORY_DONE) {
        return evs;
    }

    // Every notice that the stream's history can no longer be trusted
    // becomes one rescan, whichever of them it carries: a drop is normally
    // reported with `MUST_SCAN_SUBDIRS` beside it, but nothing guarantees
    // that, and a notice that reached the handler as no event at all would
    // be a loss the handler is never told of. The hint FSEvents gives is
    // passed through in the info attr field.
    if flags.intersects(LOSS_NOTICES) {
        let e = Event::new(EventKind::Other).set_flag(Flag::Rescan);
        evs.push(if flags.contains(StreamFlags::USER_DROPPED) {
            e.set_info("rescan: user dropped")
        } else if flags.contains(StreamFlags::KERNEL_DROPPED) {
            e.set_info("rescan: kernel dropped")
        } else if flags.contains(StreamFlags::IDS_WRAPPED) {
            e.set_info("rescan: event ids wrapped")
        } else if flags.contains(StreamFlags::ROOT_CHANGED) {
            e.set_info("rescan: root changed")
        } else {
            e
        });
    }

    // In imprecise mode, let's not even bother parsing the kind of the event
    // except for the above very special events.
    if !precise {
        evs.push(Event::new(EventKind::Any));
        return evs;
    }

    // This is most likely a rename or a removal. We assume rename but may want
    // to figure out if it was a removal some way later (TODO). To denote the
    // special nature of the event, we add an info string.
    if flags.contains(StreamFlags::ROOT_CHANGED) {
        evs.push(
            Event::new(EventKind::Modify(ModifyKind::Name(RenameMode::From)))
                .set_info("root changed"),
        );
    }

    // A path was mounted at the event path; we treat that as a create.
    if flags.contains(StreamFlags::MOUNT) {
        evs.push(Event::new(EventKind::Create(CreateKind::Other)).set_info("mount"));
    }

    // A path was unmounted at the event path; we treat that as a remove.
    if flags.contains(StreamFlags::UNMOUNT) {
        evs.push(Event::new(EventKind::Remove(RemoveKind::Other)).set_info("mount"));
    }

    if flags.contains(StreamFlags::ITEM_CREATED) {
        evs.push(if flags.contains(StreamFlags::IS_DIR) {
            Event::new(EventKind::Create(CreateKind::Folder))
        } else if flags.contains(StreamFlags::IS_FILE) {
            Event::new(EventKind::Create(CreateKind::File))
        } else {
            let e = Event::new(EventKind::Create(CreateKind::Other));
            if flags.contains(StreamFlags::IS_SYMLINK) {
                e.set_info("is: symlink")
            } else if flags.contains(StreamFlags::IS_HARDLINK) {
                e.set_info("is: hardlink")
            } else if flags.contains(StreamFlags::ITEM_CLONED) {
                e.set_info("is: clone")
            } else {
                Event::new(EventKind::Create(CreateKind::Any))
            }
        });
    }

    if flags.contains(StreamFlags::ITEM_REMOVED) {
        evs.push(if flags.contains(StreamFlags::IS_DIR) {
            Event::new(EventKind::Remove(RemoveKind::Folder))
        } else if flags.contains(StreamFlags::IS_FILE) {
            Event::new(EventKind::Remove(RemoveKind::File))
        } else {
            let e = Event::new(EventKind::Remove(RemoveKind::Other));
            if flags.contains(StreamFlags::IS_SYMLINK) {
                e.set_info("is: symlink")
            } else if flags.contains(StreamFlags::IS_HARDLINK) {
                e.set_info("is: hardlink")
            } else if flags.contains(StreamFlags::ITEM_CLONED) {
                e.set_info("is: clone")
            } else {
                Event::new(EventKind::Remove(RemoveKind::Any))
            }
        });
    }

    // FSEvents provides no mechanism to associate the old and new sides of a
    // rename event.
    if flags.contains(StreamFlags::ITEM_RENAMED) {
        evs.push(Event::new(EventKind::Modify(ModifyKind::Name(
            RenameMode::Any,
        ))));
    }

    // This is only described as "metadata changed", but it may be that it's
    // only emitted for some more precise subset of events... if so, will need
    // amending, but for now we have an Any-shaped bucket to put it in.
    if flags.contains(StreamFlags::INODE_META_MOD) {
        evs.push(Event::new(EventKind::Modify(ModifyKind::Metadata(
            MetadataKind::Any,
        ))));
    }

    if flags.contains(StreamFlags::FINDER_INFO_MOD) {
        evs.push(
            Event::new(EventKind::Modify(ModifyKind::Metadata(MetadataKind::Other)))
                .set_info("meta: finder info"),
        );
    }

    if flags.contains(StreamFlags::ITEM_CHANGE_OWNER) {
        evs.push(Event::new(EventKind::Modify(ModifyKind::Metadata(
            MetadataKind::Ownership,
        ))));
    }

    if flags.contains(StreamFlags::ITEM_XATTR_MOD) {
        evs.push(Event::new(EventKind::Modify(ModifyKind::Metadata(
            MetadataKind::Extended,
        ))));
    }

    // This is specifically described as a data change, which we take to mean
    // is a content change.
    if flags.contains(StreamFlags::ITEM_MODIFIED) {
        evs.push(Event::new(EventKind::Modify(ModifyKind::Data(
            DataChange::Content,
        ))));
    }

    if flags.contains(StreamFlags::OWN_EVENT) {
        for ev in &mut evs {
            *ev = std::mem::take(ev).set_process_id(std::process::id());
        }
    }

    evs
}

struct StreamContextInfo {
    event_handler: Arc<Mutex<dyn EventHandler>>,
    recursive_info: HashMap<PathBuf, bool>,
}

// Free the context when the stream created by `FSEventStreamCreate` is released.
extern "C" fn release_context(info: *const libc::c_void) {
    // Safety:
    // - The [documentation] for `FSEventStreamContext` states that `release` is only
    //   called when the stream is deallocated, so it is safe to convert `info` back into a
    //   box and drop it.
    //
    // [docs]: https://developer.apple.com/documentation/coreservices/fseventstreamcontext?language=objc
    unsafe {
        drop(Box::from_raw(
            info as *const StreamContextInfo as *mut StreamContextInfo,
        ));
    }
}

extern "C" {
    /// Indicates whether the run loop is waiting for an event.
    fn CFRunLoopIsWaiting(runloop: cf::CFRunLoopRef) -> cf::Boolean;
}

struct FsEventPathsMut<'a>(&'a mut FsEventWatcher);
impl<'a> FsEventPathsMut<'a> {
    fn new(watcher: &'a mut FsEventWatcher) -> Self {
        watcher.stop();
        Self(watcher)
    }
}
impl PathsMut for FsEventPathsMut<'_> {
    fn add(&mut self, path: &Path, recursive_mode: RecursiveMode) -> Result<()> {
        self.0.append_path(path, recursive_mode)
    }

    fn remove(&mut self, path: &Path) -> Result<()> {
        self.0.remove_path(path)
    }

    fn commit(self: Box<Self>) -> Result<()> {
        // ignore return error: may be empty path list
        let _ = self.0.run();
        Ok(())
    }
}

impl FsEventWatcher {
    fn from_event_handler(event_handler: Arc<Mutex<dyn EventHandler>>) -> Result<Self> {
        Ok(FsEventWatcher {
            paths: unsafe {
                cf::CFArrayCreateMutable(cf::kCFAllocatorDefault, 0, &cf::kCFTypeArrayCallBacks)
            },
            since_when: fs::kFSEventStreamEventIdSinceNow,
            latency: 0.0,
            flags: fs::kFSEventStreamCreateFlagFileEvents | fs::kFSEventStreamCreateFlagNoDefer,
            event_handler,
            runloop: None,
            recursive_info: HashMap::new(),
        })
    }

    fn watch_inner(&mut self, path: &Path, recursive_mode: RecursiveMode) -> Result<()> {
        self.stop();
        let result = self.append_path(path, recursive_mode);
        // ignore return error: may be empty path list
        let _ = self.run();
        result
    }

    fn unwatch_inner(&mut self, path: &Path) -> Result<()> {
        self.stop();
        let result = self.remove_path(path);
        // ignore return error: may be empty path list
        let _ = self.run();
        result
    }

    #[inline]
    fn is_running(&self) -> bool {
        self.runloop.is_some()
    }

    fn stop(&mut self) {
        if !self.is_running() {
            return;
        }

        if let Some((runloop, thread_handle)) = self.runloop.take() {
            unsafe {
                let runloop = runloop as *mut raw::c_void;

                while CFRunLoopIsWaiting(runloop) == 0 {
                    thread::yield_now();
                }

                cf::CFRunLoopStop(runloop);
            }

            // Wait for the thread to shut down.
            thread_handle.join().expect("thread to shut down");
        }
    }

    fn remove_path(&mut self, path: &Path) -> Result<()> {
        let str_path = path.to_str().unwrap();
        unsafe {
            let mut err: cf::CFErrorRef = ptr::null_mut();
            let cf_path = cf::str_path_to_cfstring_ref(str_path, &mut err);
            if cf_path.is_null() {
                cf::CFRelease(err as cf::CFRef);
                return Err(Error::watch_not_found().add_path(path.into()));
            }

            let mut to_remove = Vec::new();
            for idx in 0..cf::CFArrayGetCount(self.paths) {
                let item = cf::CFArrayGetValueAtIndex(self.paths, idx);
                if cf::CFStringCompare(item, cf_path, cf::kCFCompareCaseInsensitive)
                    == cf::kCFCompareEqualTo
                {
                    to_remove.push(idx);
                }
            }

            cf::CFRelease(cf_path);

            for idx in to_remove.iter().rev() {
                cf::CFArrayRemoveValueAtIndex(self.paths, *idx);
            }
        }
        let p = if let Ok(canonicalized_path) = path.canonicalize() {
            canonicalized_path
        } else {
            path.to_owned()
        };
        match self.recursive_info.remove(&p) {
            Some(_) => Ok(()),
            None => Err(Error::watch_not_found()),
        }
    }

    // https://github.com/thibaudgg/rb-fsevent/blob/master/ext/fsevent_watch/main.c
    fn append_path(&mut self, path: &Path, recursive_mode: RecursiveMode) -> Result<()> {
        if !path.exists() {
            return Err(Error::path_not_found().add_path(path.into()));
        }
        let canonical_path = path.to_path_buf().canonicalize()?;
        let str_path = path.to_str().unwrap();
        unsafe {
            let mut err: cf::CFErrorRef = ptr::null_mut();
            let cf_path = cf::str_path_to_cfstring_ref(str_path, &mut err);
            if cf_path.is_null() {
                // Most likely the directory was deleted, or permissions changed,
                // while the above code was running.
                cf::CFRelease(err as cf::CFRef);
                return Err(Error::path_not_found().add_path(path.into()));
            }
            cf::CFArrayAppendValue(self.paths, cf_path);
            cf::CFRelease(cf_path);
        }
        self.recursive_info
            .insert(canonical_path, recursive_mode.is_recursive());
        Ok(())
    }

    fn run(&mut self) -> Result<()> {
        if unsafe { cf::CFArrayGetCount(self.paths) } == 0 {
            // TODO: Reconstruct and add paths to error
            return Err(Error::path_not_found());
        }

        // We need to associate the stream context with our callback in order to propagate events
        // to the rest of the system. This will be owned by the stream, and will be freed when the
        // stream is closed. This means we will leak the context if we panic before reaching
        // `FSEventStreamRelease`.
        let context = Box::into_raw(Box::new(StreamContextInfo {
            event_handler: self.event_handler.clone(),
            recursive_info: self.recursive_info.clone(),
        }));

        let stream_context = fs::FSEventStreamContext {
            version: 0,
            info: context as *mut libc::c_void,
            retain: None,
            release: Some(release_context),
            copy_description: None,
        };

        let stream = unsafe {
            fs::FSEventStreamCreate(
                cf::kCFAllocatorDefault,
                callback,
                &stream_context,
                self.paths,
                self.since_when,
                self.latency,
                self.flags,
            )
        };

        // Wrapper to help send CFRef types across threads.
        struct CFSendWrapper(cf::CFRef);

        // Safety:
        // - According to the Apple documentation, it's safe to move `CFRef`s across threads.
        //   https://developer.apple.com/library/archive/documentation/Cocoa/Conceptual/Multithreading/ThreadSafetySummary/ThreadSafetySummary.html
        unsafe impl Send for CFSendWrapper {}

        // move into thread
        let stream = CFSendWrapper(stream);

        // channel to pass runloop around
        let (rl_tx, rl_rx) = unbounded();

        let thread_handle = thread::Builder::new()
            .name("notify-rs fsevents loop".to_string())
            .spawn(move || {
                let _ = &stream;
                let stream = stream.0;

                unsafe {
                    let cur_runloop = cf::CFRunLoopGetCurrent();

                    fs::FSEventStreamScheduleWithRunLoop(
                        stream,
                        cur_runloop,
                        cf::kCFRunLoopDefaultMode,
                    );
                    fs::FSEventStreamStart(stream);

                    // the calling to CFRunLoopRun will be terminated by CFRunLoopStop call in drop()
                    rl_tx
                        .send(CFSendWrapper(cur_runloop))
                        .expect("Unable to send runloop to watcher");

                    cf::CFRunLoopRun();
                    fs::FSEventStreamStop(stream);
                    // There are edge-cases, when many events are pending,
                    // despite the stream being stopped, that the stream's
                    // associated callback will be invoked. Purging events
                    // is intended to prevent this.
                    let event_id = fs::FSEventsGetCurrentEventId();
                    let device = fs::FSEventStreamGetDeviceBeingWatched(stream);
                    fs::FSEventsPurgeEventsForDeviceUpToEventId(device, event_id);
                    fs::FSEventStreamInvalidate(stream);
                    fs::FSEventStreamRelease(stream);
                }
            })?;
        // block until runloop has been sent
        self.runloop = Some((rl_rx.recv().unwrap().0, thread_handle));

        Ok(())
    }

    fn configure_raw_mode(&mut self, _config: Config, tx: Sender<Result<bool>>) {
        tx.send(Ok(false))
            .expect("configuration channel disconnect");
    }
}

extern "C" fn callback(
    stream_ref: fs::FSEventStreamRef,
    info: *mut libc::c_void,
    num_events: libc::size_t,                        // size_t numEvents
    event_paths: *mut libc::c_void,                  // void *eventPaths
    event_flags: *const fs::FSEventStreamEventFlags, // const FSEventStreamEventFlags eventFlags[]
    event_ids: *const fs::FSEventStreamEventId,      // const FSEventStreamEventId eventIds[]
) {
    unsafe {
        callback_impl(
            stream_ref,
            info,
            num_events,
            event_paths,
            event_flags,
            event_ids,
        )
    }
}

/// Whether an event at `path` belongs to one of the watched paths in
/// `recursive_info`: the path is watched itself, its parent is watched, or
/// one of its ancestors is watched recursively.
///
/// The path and its ancestors are looked up by hash rather than scanning
/// every watched path, so deciding an event costs one lookup per component
/// of its path, however many paths are watched. The callback runs this for
/// every event FSEvents delivers, and a scan of every watch slows delivery
/// in proportion to how many there are.
fn is_watched(recursive_info: &HashMap<PathBuf, bool>, path: &Path) -> bool {
    if recursive_info.contains_key(path) {
        return true;
    }
    path.ancestors()
        .skip(1)
        .enumerate()
        .any(|(depth, ancestor)| match recursive_info.get(ancestor) {
            Some(&recursive) => recursive || depth == 0,
            None => false,
        })
}

unsafe fn callback_impl(
    _stream_ref: fs::FSEventStreamRef,
    info: *mut libc::c_void,
    num_events: libc::size_t,                        // size_t numEvents
    event_paths: *mut libc::c_void,                  // void *eventPaths
    event_flags: *const fs::FSEventStreamEventFlags, // const FSEventStreamEventFlags eventFlags[]
    _event_ids: *const fs::FSEventStreamEventId,     // const FSEventStreamEventId eventIds[]
) {
    let event_paths = event_paths as *const *const libc::c_char;
    let info = info as *const StreamContextInfo;
    let event_handler = &(*info).event_handler;

    for p in 0..num_events {
        let path = CStr::from_ptr(*event_paths.add(p))
            .to_str()
            .expect("Invalid UTF8 string.");
        let path = PathBuf::from(path);

        let flag = *event_flags.add(p);
        let flag = StreamFlags::from_bits(flag).unwrap_or_else(|| {
            panic!("Unable to decode StreamFlags: {}", flag);
        });

        let forwarding = forwarding(&(*info).recursive_info, &path, &flag);
        if forwarding == Forwarding::Nothing {
            continue;
        }

        log::trace!("FSEvent: path = `{}`, flag = {:?}", path.display(), flag);

        let events = translate_flags(flag, true)
            .into_iter()
            .filter(|ev| forwarding == Forwarding::All || ev.need_rescan());
        for ev in events {
            // TODO: precise
            let ev = ev.add_path(path.clone());
            let mut event_handler = event_handler.lock().expect("lock not to be poisoned");
            event_handler.handle_event(Ok(ev));
        }
    }
}

impl Watcher for FsEventWatcher {
    /// Create a new watcher.
    fn new<F: EventHandler>(event_handler: F, _config: Config) -> Result<Self> {
        Self::from_event_handler(Arc::new(Mutex::new(event_handler)))
    }

    fn watch(&mut self, path: &Path, recursive_mode: RecursiveMode) -> Result<()> {
        self.watch_inner(path, recursive_mode)
    }

    fn paths_mut<'me>(&'me mut self) -> Box<dyn PathsMut + 'me> {
        Box::new(FsEventPathsMut::new(self))
    }

    fn unwatch(&mut self, path: &Path) -> Result<()> {
        self.unwatch_inner(path)
    }

    fn configure(&mut self, config: Config) -> Result<bool> {
        let (tx, rx) = unbounded();
        self.configure_raw_mode(config, tx);
        rx.recv()?
    }

    fn kind() -> crate::WatcherKind {
        crate::WatcherKind::Fsevent
    }
}

impl Drop for FsEventWatcher {
    fn drop(&mut self) {
        self.stop();
        unsafe {
            cf::CFRelease(self.paths);
        }
    }
}

#[test]
fn test_is_watched_matches_each_kind_of_watch() {
    let mut recursive_info = HashMap::new();
    recursive_info.insert(PathBuf::from("/repo"), false);
    recursive_info.insert(PathBuf::from("/repo/src"), false);
    recursive_info.insert(PathBuf::from("/deep"), true);
    recursive_info.insert(PathBuf::from("/single/file.txt"), false);

    let cases = [
        // A watched path itself, recursive or not.
        ("/repo", true),
        ("/deep", true),
        ("/single/file.txt", true),
        // A direct child of a non-recursive watch.
        ("/repo/readme.md", true),
        ("/repo/src/main.rs", true),
        // A grandchild of a non-recursive watch whose own parent is unwatched.
        ("/repo/target/debug", false),
        // Any descendant of a recursive watch.
        ("/deep/a", true),
        ("/deep/a/b/c", true),
        // A sibling sharing a prefix of characters, not of components.
        ("/repository/readme.md", false),
        ("/deeper/a", false),
        // The parent of a watched file, and its other children.
        ("/single", false),
        ("/single/other.txt", false),
        // Nothing watched above it at all.
        ("/elsewhere/x", false),
        ("/", false),
    ];
    for (path, expected) in cases {
        assert_eq!(
            is_watched(&recursive_info, Path::new(path)),
            expected,
            "{path}"
        );
    }
}

#[test]
fn test_is_watched_agrees_with_a_scan_of_every_watch() {
    // The decision a scan of every watched path makes, which `is_watched`
    // replaces: kept here as the reference it must agree with.
    fn scan(recursive_info: &HashMap<PathBuf, bool>, path: &Path) -> bool {
        recursive_info.iter().any(|(watched, &recursive)| {
            path.starts_with(watched)
                && (recursive || path == watched || path.parent() == Some(watched.as_path()))
        })
    }

    let watches: [(&str, bool); 6] = [
        ("/a", false),
        ("/a/b", true),
        ("/a/b/c", false),
        ("/x/y", false),
        ("/x/y/z.txt", false),
        ("/r", true),
    ];
    let paths = [
        "/",
        "/a",
        "/a/b",
        "/a/b/c",
        "/a/b/c/d",
        "/a/b/c/d/e",
        "/a/z",
        "/a/z/q",
        "/ab",
        "/x",
        "/x/y",
        "/x/y/z.txt",
        "/x/y/w",
        "/x/y/w/v",
        "/r",
        "/r/s/t",
        "/rs",
    ];
    // Every subset of the watches, so each path is judged against watches
    // that are recursive, non-recursive, nested in each other and absent.
    for mask in 0u32..(1 << watches.len()) {
        let recursive_info: HashMap<PathBuf, bool> = watches
            .iter()
            .enumerate()
            .filter(|(index, _)| mask & (1 << index) != 0)
            .map(|(_, &(watched, recursive))| (PathBuf::from(watched), recursive))
            .collect();
        for path in paths {
            assert_eq!(
                is_watched(&recursive_info, Path::new(path)),
                scan(&recursive_info, Path::new(path)),
                "{path} against {recursive_info:?}"
            );
        }
    }
}

/// The watches the forwarding tests decide against: a non-recursive watch
/// on a tree and one of its directories, and a recursive one elsewhere.
#[cfg(test)]
fn forwarding_watches() -> HashMap<PathBuf, bool> {
    HashMap::from([
        (PathBuf::from("/vol/repo"), false),
        (PathBuf::from("/vol/repo/src"), false),
        (PathBuf::from("/deep"), true),
    ])
}

#[test]
fn test_a_drop_or_a_wrap_hands_on_its_rescan_whatever_its_path() {
    let watches = forwarding_watches();
    for flags in [
        StreamFlags::USER_DROPPED,
        StreamFlags::KERNEL_DROPPED,
        StreamFlags::IDS_WRAPPED,
        StreamFlags::MUST_SCAN_SUBDIRS | StreamFlags::USER_DROPPED,
        StreamFlags::MUST_SCAN_SUBDIRS | StreamFlags::KERNEL_DROPPED,
    ] {
        for path in ["/", "/vol", "/elsewhere/x", "/vol/repo/target/debug"] {
            assert_eq!(
                forwarding(&watches, Path::new(path), &flags),
                Forwarding::RescanOnly,
                "{flags:?} at {path}"
            );
        }
        // At a watched path, as FSEvents delivers a user drop: once for each
        // watched path, at that path.
        assert_eq!(
            forwarding(&watches, Path::new("/vol/repo"), &flags),
            Forwarding::All,
            "{flags:?} at a watched path"
        );
    }
}

#[test]
fn test_a_subtree_notice_hands_on_its_rescan_when_its_subtree_touches_a_watch() {
    let watches = forwarding_watches();
    for flags in [StreamFlags::MUST_SCAN_SUBDIRS, StreamFlags::ROOT_CHANGED] {
        // Above every watch: the volume, and an ancestor of the tree.
        for path in ["/", "/vol"] {
            assert_eq!(
                forwarding(&watches, Path::new(path), &flags),
                Forwarding::RescanOnly,
                "{flags:?} at {path}, above a watch"
            );
        }
        // A watched path, a direct child of a non-recursive watch, and a
        // descendant of a recursive one.
        for path in ["/vol/repo", "/vol/repo/src", "/vol/repo/new", "/deep/a/b"] {
            assert_eq!(
                forwarding(&watches, Path::new(path), &flags),
                Forwarding::All,
                "{flags:?} at {path}, a watched path"
            );
        }
        // Wholly in a part no watch reports: a grandchild of a non-recursive
        // watch with nothing watched below it, and a tree watched by nothing.
        for path in ["/vol/repo/target/debug", "/elsewhere", "/vol/other"] {
            assert_eq!(
                forwarding(&watches, Path::new(path), &flags),
                Forwarding::Nothing,
                "{flags:?} at {path}, touching no watch"
            );
        }
    }
}

#[test]
fn test_an_ordinary_event_is_handed_on_only_when_its_path_is_watched() {
    let watches = forwarding_watches();
    let flags = StreamFlags::ITEM_CREATED | StreamFlags::IS_FILE;
    for path in ["/vol/repo/a.rs", "/vol/repo/src/b.rs", "/deep/a/b/c.rs"] {
        assert_eq!(
            forwarding(&watches, Path::new(path), &flags),
            Forwarding::All,
            "an event at watched {path}"
        );
    }
    // Above every watch, an ancestor of one, and in a part no watch reports:
    // an ordinary event is filtered by its path, whatever lies below it.
    for path in ["/", "/vol", "/vol/repo/target/debug/x.o", "/elsewhere/x"] {
        assert_eq!(
            forwarding(&watches, Path::new(path), &flags),
            Forwarding::Nothing,
            "an event at unwatched {path}"
        );
    }
}

#[test]
fn test_every_loss_notice_becomes_a_rescan() {
    for flags in [
        StreamFlags::MUST_SCAN_SUBDIRS,
        StreamFlags::USER_DROPPED,
        StreamFlags::KERNEL_DROPPED,
        StreamFlags::IDS_WRAPPED,
        StreamFlags::ROOT_CHANGED,
    ] {
        let name = format!("{flags:?}");
        let events = translate_flags(flags, true);
        assert_eq!(
            events.iter().filter(|event| event.need_rescan()).count(),
            1,
            "{name} became {events:?}"
        );
    }
    let ordinary = translate_flags(StreamFlags::ITEM_CREATED | StreamFlags::IS_FILE, true);
    assert!(
        ordinary.iter().all(|event| !event.need_rescan()),
        "an ordinary create became {ordinary:?}"
    );
}

/// Drives the callback itself with `delivered`, each a path and its flags, as
/// the arrays FSEvents hands it, against non-recursive watches on `watched`,
/// and returns every event the handler was given.
#[cfg(test)]
fn events_the_callback_hands_on(watched: &[&str], delivered: &[(&str, StreamFlags)]) -> Vec<Event> {
    use std::ffi::CString;

    let (tx, rx) = std::sync::mpsc::channel();
    let info = StreamContextInfo {
        event_handler: Arc::new(Mutex::new(tx)),
        recursive_info: watched
            .iter()
            .map(|path| (PathBuf::from(path), false))
            .collect(),
    };
    let paths: Vec<CString> = delivered
        .iter()
        .map(|(path, _)| CString::new(*path).expect("a path without a nul"))
        .collect();
    let path_pointers: Vec<*const libc::c_char> = paths.iter().map(|path| path.as_ptr()).collect();
    let flags: Vec<fs::FSEventStreamEventFlags> =
        delivered.iter().map(|(_, flags)| flags.bits()).collect();
    let ids = vec![0; delivered.len()];
    // Safety: every array holds `delivered.len()` elements and outlives the
    // call, and `info` is the `StreamContextInfo` the callback expects.
    unsafe {
        callback_impl(
            ptr::null_mut(),
            &info as *const StreamContextInfo as *mut libc::c_void,
            delivered.len(),
            path_pointers.as_ptr() as *mut libc::c_void,
            flags.as_ptr(),
            ids.as_ptr(),
        );
    }
    rx.try_iter()
        .map(|event| event.expect("an event"))
        .collect()
}

/// Drives the callback itself, with the arrays FSEvents hands it, so that
/// what decides forwarding there is tested and not only `forwarding`.
/// A real stream will not coalesce on demand: a drop it can be made to
/// report arrives at each watched path, which the filter before this one
/// forwarded already.
#[test]
fn test_the_callback_forwards_a_subtree_notice_above_its_watch() {
    let events = events_the_callback_hands_on(
        &["/vol/repo"],
        &[
            ("/vol", StreamFlags::MUST_SCAN_SUBDIRS),
            ("/vol/repo/target/debug", StreamFlags::MUST_SCAN_SUBDIRS),
            (
                "/vol/repo/a.rs",
                StreamFlags::ITEM_CREATED | StreamFlags::IS_FILE,
            ),
        ],
    );

    let rescans: Vec<&Event> = events.iter().filter(|event| event.need_rescan()).collect();
    assert_eq!(rescans.len(), 1, "the handler was given {events:?}");
    assert_eq!(rescans[0].paths, [PathBuf::from("/vol")]);
    assert!(
        events
            .iter()
            .any(|event| event.paths == [PathBuf::from("/vol/repo/a.rs")]),
        "the create in the watch did not arrive: {events:?}"
    );
    assert!(
        events
            .iter()
            .all(|event| event.paths != [PathBuf::from("/vol/repo/target/debug")]),
        "a notice touching no watch was forwarded: {events:?}"
    );
}

/// A notice handed on only because it reports a loss, at a path nothing
/// watches, carries its rescan and nothing else: the ordinary flags beside
/// it describe that unwatched path, which the handler never asked about.
#[test]
fn test_the_callback_hands_on_only_the_rescan_of_a_notice_at_an_unwatched_path() {
    let notice = StreamFlags::MUST_SCAN_SUBDIRS | StreamFlags::ITEM_CREATED | StreamFlags::IS_FILE;
    let events = events_the_callback_hands_on(&["/vol/repo"], &[("/vol", notice)]);

    assert_eq!(events.len(), 1, "the handler was given {events:?}");
    assert!(events[0].need_rescan(), "the handler was given {events:?}");
    assert_eq!(events[0].paths, [PathBuf::from("/vol")]);
}

#[test]
fn test_fsevent_watcher_drop() {
    use super::*;
    use std::time::Duration;

    let dir = tempfile::tempdir().unwrap();

    let (tx, rx) = std::sync::mpsc::channel();

    {
        let mut watcher = FsEventWatcher::new(tx, Default::default()).unwrap();
        watcher.watch(dir.path(), RecursiveMode::Recursive).unwrap();
        thread::sleep(Duration::from_millis(2000));
        println!("is running -> {}", watcher.is_running());

        thread::sleep(Duration::from_millis(1000));
        watcher.unwatch(dir.path()).unwrap();
        println!("is running -> {}", watcher.is_running());
    }

    thread::sleep(Duration::from_millis(1000));

    for res in rx {
        let e = res.unwrap();
        println!("debug => {:?} {:?}", e.kind, e.paths);
    }

    println!("in test: {} works", file!());
}

#[test]
fn test_steam_context_info_send_and_sync() {
    fn check_send<T: Send + Sync>() {}
    check_send::<StreamContextInfo>();
}
