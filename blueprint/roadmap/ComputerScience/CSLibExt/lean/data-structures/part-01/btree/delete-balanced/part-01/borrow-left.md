---
article_id: af_e69862c3667b1d8a722b4be9
declaration: def
origin: cited
statement: formalized
lean: Cslib.Algorithms.Lean.BTree.borrowLeft
---

# Borrow Left

Borrow for `child` from its left sibling: the separator `sep` moves
down as the child's first key (with the sibling's last child), and the
sibling's last key moves up as the new separator. Returns the new sibling,
separator, and child.

## Depends on

- [BTree](../../../btree-2/part-01/btree.md)

## Proof depends on

- [Split Last](split-last.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.BTree.DeleteBalanced](../../../../../../../../../sources/v2/CSLibExt.md)
