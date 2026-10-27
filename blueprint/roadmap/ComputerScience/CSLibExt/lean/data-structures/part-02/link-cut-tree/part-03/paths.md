---
article_id: af_b0d004373a45de4f98a75c6e
declaration: def
origin: cited
statement: formalized
lean: Cslib.Algorithms.Lean.LinkCutTree.State.paths
---

# Paths

The preferred-path decomposition of a state: in each represented tree,
the maximal chains of preferred edges (`treePaths`), deepest continuation
last within each path. Vertices incident to no preferred edge are singleton
paths. Unlike a single distinguished path, this retains the preferred paths
of every subtree: only edges incident to the latest accessed root path
change under `access`.

## Depends on

- [State](state.md)

## Proof depends on

- [Tree](../../euler-tour-tree/part-01/tree.md)
- [Tree Paths](tree-paths.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.LinkCutTree](../../../../../../../../sources/v2/CSLibExt.md)
