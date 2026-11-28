# Heap Merge

The `Heap_Merge` locale (`HOL-Data_Structures.Heaps`), as a structure:
a merge operation together with its two defining properties.
Isabelle's locale also defines `insert`, `del_min`, `get_min` from
`merge`; in this file those are the file-level `insert` / `delMin` /
`getMin` below, defined from `SkewHeap.merge` in exactly the same way.
