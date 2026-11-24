# Tag Sort Slice Occurrences

Attach an absolute occurrence index to every key in a complete
`SortSlice`, without changing the payload paired with that key.  Tagging the
whole slice before selecting a range prevents a nonzero-base subrange from
being accidentally retagged relative to zero.
