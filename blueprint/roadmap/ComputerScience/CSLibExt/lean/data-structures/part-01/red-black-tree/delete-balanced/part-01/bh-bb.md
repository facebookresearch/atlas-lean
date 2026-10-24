---
article_id: af_34817c4b94c5f8d20bea0517
declaration: def
origin: cited
statement: formalized
lean: Cslib.Algorithms.Lean.RedBlackTree.DeleteBalanced.bhBB
---

# Bh BB

The black height of a `BBTree`: a double-black root counts as two black
nodes, so `bhBB` of a deletion result equals `blackHeight` of the original
tree.

## Depends on

- [BBTree](bbtree.md)

## Proof depends on

- [Tree](../../../../part-03/red-black-tree/part-01/tree.md)
- [Black Height](../../../../part-03/red-black-tree/part-01/black-height.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.RedBlackTree.DeleteBalanced](../../../../../../../../../sources/v2/CSLibExt.md)
