---
article_id: af_388ffc7fd6f912dbb8722add
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.BTree.deleteRebuild_validRoot
---

# Delete Rebuild valid Root

The result of a deletion is root-valid at some height: some uniform height
at which every non-root node holds between `t - 1` and `2 * t - 1` keys. The
height is that of the rebuilt tree; no relation to the height of the input
is claimed (see the module documentation).

## Depends on

- [BTree](../../btree-2/part-01/btree.md)
- [Valid Root](../../btree-2/part-01/valid-root.md)
- [Delete Rebuild](delete-rebuild.md)

## Proof depends on

- [Delete Rebuild](delete-rebuild-2.md)
- [Exists valid Root](../../btree-2/part-02/exists-valid-root.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.BTree.Delete](../../../../../../../../sources/v2/CSLibExt.md)
