---
article_id: af_7a6ec5b7c7a58aea78979e4f
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.BTree.contains_delete_iff
---

# Contains delete iff

Search in the result of a deletion agrees with membership in the
original tree minus the deleted key.

## Depends on

- [BTree](../../../btree-2/part-01/btree.md)
- [Is BTree](../../../btree-2/part-02/is-btree.md)
- [Mem](../../../btree-2/part-01/mem.md)
- [Contains](../../../btree-2/part-01/contains.md)
- [Delete](delete.md)

## Proof depends on

- [Delete](delete-2.md)
- [Contains eq true iff](../../../btree-2/part-02/contains-eq-true-iff.md)
- [Mem delete](mem-delete.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.BTree.DeleteBalanced](../../../../../../../../../sources/v2/CSLibExt.md)
