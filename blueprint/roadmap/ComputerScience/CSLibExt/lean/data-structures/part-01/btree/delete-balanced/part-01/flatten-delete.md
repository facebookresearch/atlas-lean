---
article_id: af_e49f9b92da50846b454843c9
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.BTree.flatten_delete
---

# Flatten delete

The flattening of a deletion from a B-tree is the erasure of the key
from the flattening of the original tree.

## Depends on

- [BTree](../../../btree-2/part-01/btree.md)
- [Is BTree](../../../btree-2/part-02/is-btree.md)
- [Delete](delete.md)
- [Flatten](../../../btree-2/part-01/flatten.md)

## Proof depends on

- [Mem](../../../btree-2/part-01/mem.md)
- [Ordered](../../../btree-2/part-01/ordered.md)
- [Valid](../../../btree-2/part-01/valid.md)
- [Valid Root](../../../btree-2/part-01/valid-root.md)
- [Valid](../../../btree-2/part-01/valid-2.md)
- [Borrow Left](borrow-left.md)
- [Borrow Right](borrow-right.md)
- [Del H](del-h.md)
- [Del List](del-list.md)
- [Flatten Aux](../../../btree-2/part-01/flatten-aux.md)
- [Flatten Aux eq](../../../btree-2/part-01/flatten-aux-eq.md)
- [Flatten node append cons](../../../btree-2/part-01/flatten-node-append-cons.md)
- [Flatten node cons nil](../../../btree-2/part-01/flatten-node-cons-nil.md)
- [Flatten node nil cons](../../../btree-2/part-01/flatten-node-nil-cons.md)
- [Flatten node nil nil](../../../btree-2/part-01/flatten-node-nil-nil.md)
- [Key Count](key-count.md)
- [Max Key](max-key.md)
- [Merge](merge.md)
- [Min Key](min-key.md)
- [Split Last](split-last.md)
- [Tree Height](tree-height.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.BTree.DeleteBalanced](../../../../../../../../../sources/v2/CSLibExt.md)
