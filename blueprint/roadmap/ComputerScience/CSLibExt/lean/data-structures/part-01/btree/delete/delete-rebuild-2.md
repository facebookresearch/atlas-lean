---
article_id: af_c42296e2c76573362418bc83
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.BTree.IsBTree.deleteRebuild
---

# Delete Rebuild

The result of a deletion is a B-tree: ordered, and root-valid at some
height, hence satisfying the occupancy bounds and uniform height of
`Valid`/`ValidRoot`. This holds for every input tree, because the result is
built by `fromList`.

## Depends on

- [BTree](../../btree-2/part-01/btree.md)
- [Is BTree](../../btree-2/part-02/is-btree.md)
- [Delete Rebuild](delete-rebuild.md)

## Proof depends on

- [From List](../../btree-2/part-02/from-list-2.md)
- [Flatten](../../btree-2/part-01/flatten.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.BTree.Delete](../../../../../../../../sources/v2/CSLibExt.md)
