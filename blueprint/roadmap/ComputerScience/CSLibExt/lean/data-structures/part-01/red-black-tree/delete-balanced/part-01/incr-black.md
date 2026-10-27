---
article_id: af_f90f738fa79f48de823bdfb7
declaration: def
origin: cited
statement: formalized
lean: Cslib.Algorithms.Lean.RedBlackTree.DeleteBalanced.incrBlack
---

# Incr Black

Add one black node to the root of a genuine tree: the empty tree becomes
double-black empty, a red root becomes black, and a black root becomes
double black.

## Depends on

- [BBTree](bbtree.md)
- [Tree](../../../../part-03/red-black-tree/part-01/tree.md)

## Proof depends on

- [Color](../../../../part-03/red-black-tree/part-01/color.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.RedBlackTree.DeleteBalanced](../../../../../../../../../sources/v2/CSLibExt.md)
