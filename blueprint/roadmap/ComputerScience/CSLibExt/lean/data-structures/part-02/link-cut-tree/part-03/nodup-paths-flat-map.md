---
article_id: af_ed43ff57fd9ed84065731e96
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.LinkCutTree.State.nodup_paths_flatMap
---

# Nodup paths flat Map

The flattened decomposition is duplicate-free: every vertex of a valid
state lies on exactly one preferred path. With `mem_paths_flatMap`, the
paths partition the vertex set.

## Depends on

- [State](state.md)
- [Valid](valid.md)
- [Paths](paths.md)

## Proof depends on

- [Tree](../../euler-tour-tree/part-01/tree.md)
- [Vertices](../../euler-tour-tree/part-01/vertices.md)
- [Parent Child](../part-02/parent-child.md)
- [Perm tree Paths flat Map](perm-tree-paths-flat-map.md)
- [Tree Paths](tree-paths.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.LinkCutTree](../../../../../../../../sources/v2/CSLibExt.md)
