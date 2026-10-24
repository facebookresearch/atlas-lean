---
article_id: af_9cf4719180bc3af6d44a3875
declaration: def
origin: cited
statement: formalized
lean: Cslib.Algorithms.Lean.FenwickTree.build
---

# Build

Build a Fenwick tree representing the given array by computing every
interval sum. The input is converted to an `Array` once, so each entry read
is constant-time and construction is `O(n log n)`.

## Depends on

- [Fenwick Tree](fenwick-tree.md)

## Proof depends on

- [Block Sum Array](block-sum-array.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.FenwickTree](../../../../../../../../sources/v2/CSLibExt.md)
