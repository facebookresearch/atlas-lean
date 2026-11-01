---
article_id: af_23b8cbe20cfd4421b760fe47
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.BinarySearchTree.ordered_join
---

# Ordered join

Splicing two ordered trees stays ordered when every key of the left tree is
smaller than every key of the right tree.

## Depends on

- [Mem](../../../part-02/binary-search-tree/part-01/mem.md)
- [Ordered](../../../part-02/binary-search-tree/part-01/ordered.md)
- [Join](join.md)

## Proof depends on

- [All](../../../part-02/binary-search-tree/part-01/all.md)
- [All iff forall mem](../../../part-02/binary-search-tree/part-01/all-iff-forall-mem.md)
- [Mem join](mem-join.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.BinarySearchTree.Delete](../../../../../../../../sources/v2/CSLibExt.md)
