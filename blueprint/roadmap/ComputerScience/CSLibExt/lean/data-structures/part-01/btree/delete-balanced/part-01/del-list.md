---
article_id: af_f8c155f2e7d065cca4e9271a
declaration: def
origin: cited
statement: formalized
lean: Cslib.Algorithms.Lean.BTree.delList
---

# Del List

Delete a key from the node with the given separator and child lists,
where `delChild` deletes from a child (in `delH`, deletion at the next
height down). Before descending into a child with fewer than `t` keys, the
child is given a key by borrowing from an adjacent sibling or is merged
with the separator and a sibling, so `delChild` is only ever applied to a
tree holding at least `t` keys at its root (or to a merged tree). The walk
goes from the left: a child that is not last borrows or merges on its
right, and the last child borrows or merges on its left, where its left
sibling and separator are in hand.

## Depends on

- [BTree](../../../btree-2/part-01/btree.md)

## Proof depends on

- [Borrow Left](borrow-left.md)
- [Borrow Right](borrow-right.md)
- [Key Count](key-count.md)
- [Max Key](max-key.md)
- [Merge](merge.md)
- [Min Key](min-key.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.BTree.DeleteBalanced](../../../../../../../../../sources/v2/CSLibExt.md)
