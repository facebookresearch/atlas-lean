---
article_id: af_d68273ac4ae7b33ce9530510
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.BTree.IsBTree.insert
---

# Insert

Insertion preserves the B-tree invariant: the result is again ordered and root-valid
(at the same height, or one taller when the root split).

## Depends on

- [BTree](../part-01/btree.md)
- [Is BTree](is-btree.md)
- [Insert](insert.md)

## Proof depends on

- [Ins Result](../part-01/ins-result.md)
- [Ordered](../part-01/ordered.md)
- [Valid](../part-01/valid.md)
- [Valid Root](../part-01/valid-root.md)
- [Flatten](../part-01/flatten.md)
- [Flatten Aux](../part-01/flatten-aux.md)
- [Flatten Aux eq](../part-01/flatten-aux-eq.md)
- [Flatten insert](flatten-insert.md)
- [Flatten node append cons](../part-01/flatten-node-append-cons.md)
- [Flatten node nil cons](../part-01/flatten-node-nil-cons.md)
- [Flatten node nil nil](../part-01/flatten-node-nil-nil.md)
- [Grown Flatten](../part-01/grown-flatten.md)
- [Ins](ins.md)
- [Ins Leaf](../part-01/ins-leaf.md)
- [Mk Node](mk-node.md)
- [Split Node](split-node.md)
- [Mem ordered Insert](../../../part-02/ordered-insert/mem-ordered-insert.md)
- [Ordered Insert](../../../part-02/ordered-insert/ordered-insert.md)
- [Ordered Insert eq of mem](../../../part-02/ordered-insert/ordered-insert-eq-of-mem.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.BTree](../../../../../../../../sources/v2/CSLibExt.md)
