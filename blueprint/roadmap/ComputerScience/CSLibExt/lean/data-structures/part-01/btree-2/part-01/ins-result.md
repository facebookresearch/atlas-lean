---
article_id: af_83a42752ecb93dbf53f2213b
declaration: def
origin: cited
statement: formalized
lean: Cslib.Algorithms.Lean.BTree.InsResult
---

# Ins Result

The result of inserting into a subtree: `.inl` holds a single tree of the same height,
and `.inr (left, median, right)` holds two trees of the same height produced by splitting a
full node, together with the median key promoted between them.

## Depends on

This node has no prerequisites.

## Proof depends on

- [BTree](btree.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.BTree](../../../../../../../../sources/v2/CSLibExt.md)
