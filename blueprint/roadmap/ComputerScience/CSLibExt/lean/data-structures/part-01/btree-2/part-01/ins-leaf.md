---
article_id: af_b773b59a652e5384cbb4574d
declaration: def
origin: cited
statement: formalized
lean: Cslib.Algorithms.Lean.BTree.insLeaf
---

# Ins Leaf

Insert into a leaf's key list, splitting the leaf around the median key when the
inserted list exceeds `2 * t - 1` keys.

## Depends on

- [Ins Result](ins-result.md)

## Proof depends on

- [BTree](btree.md)
- [Ordered Insert](../../../part-02/ordered-insert/ordered-insert.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.BTree](../../../../../../../../sources/v2/CSLibExt.md)
