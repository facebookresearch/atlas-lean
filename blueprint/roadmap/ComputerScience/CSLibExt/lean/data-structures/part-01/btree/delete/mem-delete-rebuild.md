---
article_id: af_68682c040423743bddb27c99
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.BTree.mem_deleteRebuild
---

# Mem delete Rebuild

A key is in the result of a deletion exactly when it was in the original
tree and is not the deleted key.

## Depends on

- [BTree](../../btree-2/part-01/btree.md)
- [Is BTree](../../btree-2/part-02/is-btree.md)
- [Mem](../../btree-2/part-01/mem.md)
- [Delete Rebuild](delete-rebuild.md)

## Proof depends on

- [Ordered](../../btree-2/part-02/ordered.md)
- [Flatten nodup](../../btree-2/part-01/flatten-nodup.md)
- [Flatten](../../btree-2/part-01/flatten.md)
- [Flatten delete Rebuild](flatten-delete-rebuild.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.BTree.Delete](../../../../../../../../sources/v2/CSLibExt.md)
