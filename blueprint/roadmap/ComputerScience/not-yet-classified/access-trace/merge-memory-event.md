# Merge Memory Event

Chronological merge-memory boundary observations.

These constructors are intentionally non-validating.  They retain enough raw
data for a separate lifecycle predicate to compare the snapshots with
`merge_init`, `merge_getmem`, the directional merge, and `merge_freemem`
without making any of those obligations true by construction.
