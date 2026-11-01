---
article_id: af_fd3c60370b75c4dab6550891
declaration: def
origin: cited
statement: formalized
lean: Cslib.Algorithms.Lean.FenwickTree.add
---

# Add

Add `δ` to underlying entry `i` by walking `i + 1, j + lowbit j, …` and adding
`δ` to exactly those stored entries; each write is constant-time only when
the stored array is uniquely referenced, since a shared array is copied by
the first persistent `Array.set`. An out-of-range
`i` visits no index and leaves the tree unchanged. The walk is fuelled by the
size, which always suffices because visited indices strictly increase.

## Depends on

- [Fenwick Tree](../part-01/fenwick-tree.md)

## Proof depends on

- [Lowbit](../part-01/lowbit.md)
- [Size](../part-01/size.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.FenwickTree](../../../../../../../../sources/v2/CSLibExt.md)
