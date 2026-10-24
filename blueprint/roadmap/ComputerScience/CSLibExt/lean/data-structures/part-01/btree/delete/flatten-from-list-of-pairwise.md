---
article_id: af_c9486f6e64aa26956e05cb9e
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.BTree.flatten_fromList_of_pairwise
---

# Flatten from List of pairwise

Building a tree from a strictly increasing list returns exactly that list
as the flattening. This is the specification of `fromList` on sorted input
that the specification of `deleteRebuild` is reduced to.

## Depends on

- [Flatten](../../btree-2/part-01/flatten.md)
- [From List](../../btree-2/part-02/from-list.md)

## Proof depends on

- [BTree](../../btree-2/part-01/btree.md)
- [From List](../../btree-2/part-02/from-list-2.md)
- [Flatten Aux](../../btree-2/part-01/flatten-aux.md)
- [Flatten insert](../../btree-2/part-02/flatten-insert.md)
- [Ordered Insert](../../../part-02/ordered-insert/ordered-insert.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.BTree.Delete](../../../../../../../../sources/v2/CSLibExt.md)
