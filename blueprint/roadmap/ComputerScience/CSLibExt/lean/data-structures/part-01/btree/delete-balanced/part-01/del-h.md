---
article_id: af_9fb4d39da59b3061ecdce281
declaration: def
origin: cited
statement: formalized
lean: Cslib.Algorithms.Lean.BTree.delH
---

# Del H

Delete a key from a tree of the given height, by a top-down pass
(with the two spine traversals in the separator case described in the
module documentation): at a leaf erase the key, and at an internal node
run `delList` with
deletion at the children's height. Heights that do not match the shape of
the tree fall back to leaf erasure or the identity; the specification
`delH_spec` only covers matching heights.

## Depends on

- [BTree](../../../btree-2/part-01/btree.md)

## Proof depends on

- [Del List](del-list.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.BTree.DeleteBalanced](../../../../../../../../../sources/v2/CSLibExt.md)
