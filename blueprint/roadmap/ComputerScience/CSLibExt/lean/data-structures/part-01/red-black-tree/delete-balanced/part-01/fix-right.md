---
article_id: af_a5fe32ffd0a988fa6f61c664
declaration: def
origin: cited
statement: formalized
lean: Cslib.Algorithms.Lean.RedBlackTree.DeleteBalanced.fixRight
---

# Fix Right

Repair a black-height deficit in the right child; the mirror image of
`fixLeft`. Here `right` is the deficient subtree with its double black
absorbed, so `blackHeight right + 1 = blackHeight left`.

## Depends on

- [Color](../../../../part-03/red-black-tree/part-01/color.md)
- [BBTree](bbtree.md)
- [Tree](../../../../part-03/red-black-tree/part-01/tree.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.RedBlackTree.DeleteBalanced](../../../../../../../../../sources/v2/CSLibExt.md)
