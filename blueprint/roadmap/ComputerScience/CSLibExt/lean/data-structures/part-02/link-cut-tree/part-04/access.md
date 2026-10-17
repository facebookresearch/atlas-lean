---
article_id: af_473362bd894353c5fb392108
declaration: def
origin: cited
statement: formalized
lean: Cslib.Algorithms.Lean.LinkCutTree.State.access
---

# Access

Make the path from the represented root to `x` preferred, as in the
textbook `access`. Every edge of the root-to-`x` path becomes solid, the
previously preferred child edge of each vertex on that path is dropped
(made dashed), and every preferred edge whose parent endpoint lies off the
path is retained: this is what keeps off-path preferred paths alive across
accesses (for example, with root `1`, children `2 → 4` and `3 → 5`,
`access 5` after `access 4` keeps the preferred path `[2, 4]`, since the
edge `2`-`4` has parent endpoint off the `1`-`3`-`5` path; see the
regression tests in `LinkCutTreeTests`). The represented forest is
unchanged. On a vertex outside the forest this is the identity.

## Depends on

- [State](../part-03/state.md)

## Proof depends on

- [Tree](../../euler-tour-tree/part-01/tree.md)
- [Find Tree](../part-01/find-tree.md)
- [Path Edges](../part-02/path-edges.md)
- [Root Path](../part-02/root-path.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.LinkCutTree](../../../../../../../../sources/v2/CSLibExt.md)
