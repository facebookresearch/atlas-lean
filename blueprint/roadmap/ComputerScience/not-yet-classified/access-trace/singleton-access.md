# Singleton Access

Low-level constructor for one access-attempt trace.  It intentionally
accepts an explicit region and extent so the typed wrappers later in this file
can share one implementation.  Instrumented listsort code should use those
state-derived wrappers instead of manufacturing labels or extents itself.  No
bounds or liveness filter is applied: rejected attempts remain observable.
