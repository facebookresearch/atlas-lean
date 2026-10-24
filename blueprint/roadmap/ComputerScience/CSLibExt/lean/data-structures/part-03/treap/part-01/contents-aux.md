---
article_id: af_5b4ec390b3e67434b661acc5
declaration: def
origin: cited
statement: formalized
lean: Cslib.Algorithms.Lean.Treap.Tree.contentsAux
---

# Contents Aux

Append the inorder key-value traversal of a tree to a suffix in linear
time: the left traversal is accumulated onto the node entry and the already
traversed right suffix, so no ancestor recopies a completed traversal.

## Depends on

- [Tree](tree.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.Treap](../../../../../../../../sources/v2/CSLibExt.md)
