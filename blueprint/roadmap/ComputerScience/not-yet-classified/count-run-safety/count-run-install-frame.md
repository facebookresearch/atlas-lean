# Count Run install frame

Installing the returned slice changes no `MergeState` field other than
`data`; in particular pending runs, comparator, temporary storage, and all
adaptive counters remain frame-stable.
