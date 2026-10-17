---
article_id: af_c353f8fa26a5e247fde95421
declaration: def
origin: cited
statement: formalized
lean: Cslib.Algorithms.Lean.RedBlackTree.DeleteBalanced.balLeft
---

# Bal Left

Reassemble a node whose left subtree was deleted from: if the result is
genuine, rebuild the node; if it is double black, repair the deficit against
the right sibling with `fixLeft`.

## Depends on

- [Color](../../../../part-03/red-black-tree/part-01/color.md)
- [BBTree](bbtree.md)
- [Tree](../../../../part-03/red-black-tree/part-01/tree.md)

## Proof depends on

- [Fix Left](fix-left.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.RedBlackTree.DeleteBalanced](../../../../../../../../../sources/v2/CSLibExt.md)
