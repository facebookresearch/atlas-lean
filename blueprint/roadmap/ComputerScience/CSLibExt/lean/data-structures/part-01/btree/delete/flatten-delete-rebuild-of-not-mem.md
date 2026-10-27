---
article_id: af_3d7b03caf0f2c118ebaeda03
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.BTree.flatten_deleteRebuild_of_not_mem
---

# Flatten delete Rebuild of not mem

Deleting an absent key leaves the flattening, hence the stored set,
unchanged. The tree itself may be rebuilt to a different shape with the same
flattening.

## Depends on

- [BTree](../../btree-2/part-01/btree.md)
- [Ordered](../../btree-2/part-01/ordered.md)
- [Delete Rebuild](delete-rebuild.md)
- [Flatten](../../btree-2/part-01/flatten.md)

## Proof depends on

- [Flatten delete Rebuild](flatten-delete-rebuild.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.BTree.Delete](../../../../../../../../sources/v2/CSLibExt.md)
