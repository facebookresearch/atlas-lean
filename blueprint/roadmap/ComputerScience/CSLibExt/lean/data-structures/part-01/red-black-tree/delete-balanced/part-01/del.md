---
article_id: af_bda168b95a7db4dc74e8de31
declaration: def
origin: cited
statement: formalized
lean: Cslib.Algorithms.Lean.RedBlackTree.DeleteBalanced.del
---

# Del

Delete a key from a genuine tree, returning a tree whose root may be
double black. A node with two children is deleted by promoting its
successor, the minimum key of its right subtree.

## Depends on

- [BBTree](bbtree.md)
- [Tree](../../../../part-03/red-black-tree/part-01/tree.md)

## Proof depends on

- [Color](../../../../part-03/red-black-tree/part-01/color.md)
- [Bal Left](bal-left.md)
- [Bal Right](bal-right.md)
- [Incr Black](incr-black.md)
- [Min Key](min-key.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.RedBlackTree.DeleteBalanced](../../../../../../../../../sources/v2/CSLibExt.md)
