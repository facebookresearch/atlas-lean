---
article_id: af_8ded4658dc9f9dfb20eddef5
declaration: def
origin: cited
statement: formalized
lean: Cslib.Algorithms.Lean.BTree.Mem
---

# Mem

Membership in a tree is membership in its flattening. The structural reading is
`mem_node`: a key is in a node when it is one of the separators or in one of the children.

## Depends on

- [BTree](btree.md)

## Proof depends on

- [Flatten](flatten.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.BTree](../../../../../../../../sources/v2/CSLibExt.md)
