---
article_id: af_b1afed75a45dedf327e1cf5f
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.LinkCutTree.State.mem_preferred_access
---

# Mem preferred access

An off-path preferred edge survives `access x`: an edge whose parent
endpoint does not lie on the root-to-`x` path is retained. This is the
edge-level statement behind retaining off-path preferred paths.

## Depends on

- [Tree](../../euler-tour-tree/part-01/tree.md)
- [State](../part-03/state.md)
- [Access](access.md)
- [Find Tree](../part-01/find-tree.md)
- [Root Path](../part-02/root-path.md)

## Proof depends on

- [Path Edges](../part-02/path-edges.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.LinkCutTree](../../../../../../../../sources/v2/CSLibExt.md)
