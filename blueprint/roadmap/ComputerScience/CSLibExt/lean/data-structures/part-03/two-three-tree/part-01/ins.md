---
article_id: af_b7f6e84ab21b33b84b0aab9b
declaration: def
origin: cited
statement: formalized
lean: Cslib.Algorithms.Lean.TwoThreeTree.ins
---

# Ins

Insert a key into a height-indexed tree, returning an `Overflow`. A leaf
always splits; a 2-node absorbs a split child by becoming a 3-node; a 3-node
with a split child splits in turn, promoting the appropriate separator. Inserting
a key equal to a separator leaves the tree unchanged.

## Depends on

- [Overflow](overflow.md)
- [Tree](tree.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.TwoThreeTree](../../../../../../../../sources/v2/CSLibExt.md)
