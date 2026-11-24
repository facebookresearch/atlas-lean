# Merge Memory Snapshot

The storage facts retained at one merge-memory boundary.

The snapshot deliberately contains only decidable, type-erased observations.
`mainValuePresent` records, in main-array order, whether each entry carries a
synchronized value.  It records the raw state rather than a Boolean claiming
that any storage invariant holds; later safety modules must validate the
snapshot independently.
