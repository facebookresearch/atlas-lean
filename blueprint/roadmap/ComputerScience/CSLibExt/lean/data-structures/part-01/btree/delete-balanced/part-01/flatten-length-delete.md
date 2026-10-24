---
article_id: af_f8754e622d4a8de50308fb98
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.BTree.flatten_length_delete
---

# Flatten length delete

Deleting a key decreases the number of stored keys by one when the key
was present, and leaves it unchanged otherwise.

## Depends on

- [BTree](../../../btree-2/part-01/btree.md)
- [Is BTree](../../../btree-2/part-02/is-btree.md)
- [Delete](delete.md)
- [Flatten](../../../btree-2/part-01/flatten.md)

## Proof depends on

- [Flatten delete](flatten-delete.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.BTree.DeleteBalanced](../../../../../../../../../sources/v2/CSLibExt.md)
