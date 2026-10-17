---
article_id: af_ef5c09e7cd654252b0b263a0
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.BTree.flatten_deleteRebuild
---

# Flatten delete Rebuild

The flattening of a deletion is the erasure of the key from the flattening
of the original tree. Orderedness is the side condition; no occupancy
hypothesis on the input beyond `2 ≤ t` is needed.

## Depends on

- [BTree](../../btree-2/part-01/btree.md)
- [Ordered](../../btree-2/part-01/ordered.md)
- [Delete Rebuild](delete-rebuild.md)
- [Flatten](../../btree-2/part-01/flatten.md)

## Proof depends on

- [Flatten from List of pairwise](flatten-from-list-of-pairwise.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.BTree.Delete](../../../../../../../../sources/v2/CSLibExt.md)
