---
article_id: af_c767ba1c3e14904b003d2334
declaration: def
origin: cited
statement: formalized
lean: Cslib.Algorithms.Lean.BTree.borrowRight
---

# Borrow Right

Borrow for `child` from its right sibling: the separator `sep` moves
down as the child's last key (with the sibling's first child), and the
sibling's first key moves up as the new separator. Returns the new child,
separator, and sibling.

## Depends on

- [BTree](../../../btree-2/part-01/btree.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.BTree.DeleteBalanced](../../../../../../../../../sources/v2/CSLibExt.md)
