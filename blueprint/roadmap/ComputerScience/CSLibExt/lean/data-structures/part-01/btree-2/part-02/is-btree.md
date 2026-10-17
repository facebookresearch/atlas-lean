---
article_id: af_2eba28d9da2c07fa0d150ff6
declaration: def
origin: cited
statement: formalized
lean: Cslib.Algorithms.Lean.BTree.IsBTree
---

# Is BTree

A tree is a B-tree of minimum degree `t` when `2 ≤ t` (the CLRS Chapter 18
minimum-degree requirement), it is ordered, and it is root-valid at some height.
This is the invariant maintained by `insert` and `fromList`.

## Depends on

- [BTree](../part-01/btree.md)

## Proof depends on

- [Ordered](../part-01/ordered.md)
- [Valid Root](../part-01/valid-root.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.BTree](../../../../../../../../sources/v2/CSLibExt.md)
