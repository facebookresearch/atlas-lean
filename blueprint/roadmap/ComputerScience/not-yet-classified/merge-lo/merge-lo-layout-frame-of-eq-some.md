# Merge Lo layout frame of eq some

A successful `merge_lo` preserves every structural field used by
`PendingLayout`, even though it may rewrite entries in the fixed-size data
array and mutate merge-specific state.
