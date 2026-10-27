---
article_id: af_d5885cb8dcbe1ad46f9a0376
declaration: def
origin: cited
statement: formalized
lean: Cslib.Algorithms.Lean.FenwickTree.blockSumArray
---

# Block Sum Array

Array-backed interval sum: like `blockSum`, but reads through an `Array`
in constant time per entry instead of traversing a `List` per lookup. This
is the version used by `build`, so construction takes `O(n log n)` reads
rather than quadratic list indexing.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Lowbit](lowbit.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.FenwickTree](../../../../../../../../sources/v2/CSLibExt.md)
