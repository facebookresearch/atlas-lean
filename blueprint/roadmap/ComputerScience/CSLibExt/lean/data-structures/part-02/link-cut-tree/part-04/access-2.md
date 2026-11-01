---
article_id: af_3949a77ecf429e039fc82e5a
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.LinkCutTree.State.Valid.access
---

# Access

Access preserves the state invariant: the new preferred edges are the
retained off-path edges together with the edges of the accessed root path;
the two groups have disjoint parent endpoints (off versus on the path), so
duplicate-freeness and the at-most-one-preferred-child condition carry over.

## Depends on

- [State](../part-03/state.md)
- [Valid](../part-03/valid.md)
- [Access](access.md)

## Proof depends on

- [Tree](../../euler-tour-tree/part-01/tree.md)
- [Vertices](../../euler-tour-tree/part-01/vertices.md)
- [Parent Child](../part-02/parent-child.md)
- [Find Tree](../part-01/find-tree.md)
- [Is Chain parent Child root Path](../part-02/is-chain-parent-child-root-path.md)
- [Nodup root Path](../part-02/nodup-root-path.md)
- [Path Edges](../part-02/path-edges.md)
- [Root Path](../part-02/root-path.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.LinkCutTree](../../../../../../../../sources/v2/CSLibExt.md)
