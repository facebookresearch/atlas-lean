---
article_id: af_4f3470990ebf4d8a4299b0ec
declaration: def
origin: cited
statement: formalized
lean: Cslib.Algorithms.Lean.BTree.flattenAux
---

# Flatten Aux

Append the inorder traversal of a tree to an existing suffix in linear
time: subtrees interleaved with separator keys, accumulated without
recopying left results. The suffix is built right to left: at an internal
node the suffix passed to each child already holds everything to its right,
so `flattenAux child suffix` only prepends that child's keys, and each key
is copied once (as part of its node's key list at a leaf, or by one `cons`
for a separator). Children or keys beyond the interleaving pattern of a
well-formed node are appended in order (see `flatten`), so every key of
the tree occurs in the result.

## Depends on

- [BTree](btree.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.BTree](../../../../../../../../sources/v2/CSLibExt.md)
