---
article_id: af_7ea3c4e9484b167bd0854e53
declaration: inductive
origin: cited
statement: formalized
lean: Cslib.Algorithms.Lean.RangeTree.BoundsOk
---

# Bounds Ok

The cached node intervals are the true leaf intervals:
at every node, `lo = min left.tmin right.tmin` and
`hi = max left.tmax right.tmax`, recursively. Node children must be
nonempty: `tmin`/`tmax` give the empty tree the sentinel `0`, so with an
empty child the node cache would only conservatively enclose the leaves
(for example `.node 0 5 .empty (.leaf 5)` would cache `[0, 5]` for the
single leaf `5`), not equal the true leaf interval. Together
`bounds_of_mem` and `bounds_mem_toList_of_ne_nil` show the cache is
exactly attained by leaves.

## Depends on

- [Range Tree](range-tree.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.RangeTree](../../../../../../../../sources/v2/CSLibExt.md)
