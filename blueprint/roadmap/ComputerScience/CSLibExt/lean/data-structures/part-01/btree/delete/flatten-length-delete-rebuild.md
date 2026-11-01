---
article_id: af_3c93a459181030eda360690d
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.BTree.flatten_length_deleteRebuild
---

# Flatten length delete Rebuild

Deleting a key decreases the number of stored keys by one when the key was
present, and leaves it unchanged otherwise.

## Depends on

- [BTree](../../btree-2/part-01/btree.md)
- [Ordered](../../btree-2/part-01/ordered.md)
- [Delete Rebuild](delete-rebuild.md)
- [Flatten](../../btree-2/part-01/flatten.md)

## Proof depends on

- [Flatten delete Rebuild](flatten-delete-rebuild.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.BTree.Delete](../../../../../../../../sources/v2/CSLibExt.md)
