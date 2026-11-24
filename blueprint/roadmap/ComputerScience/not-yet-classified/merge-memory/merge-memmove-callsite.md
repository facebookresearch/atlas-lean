# Merge Memmove Callsite

The four block-movement sites whose source and destination are both in
`MergeState.data`.  They are deliberately separate from the six tagged
temp/main `memcpy` sites: these calls require overlap-safe `memmove` semantics.
