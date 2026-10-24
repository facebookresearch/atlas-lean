---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.Hierholzer.visit_spec
---

# Visit spec

The contract of `visit`: given more fuel than remaining edges and a remaining multigraph
unbalanced only by `v → … → t`, the call emits a walk `W` from `v` to `t` in front of `acc`,
removes exactly its steps, leaves a balanced remainder in which `W`'s vertices have no outgoing
edges, only shortens adjacency lists, and costs one unit per removed edge.

## Depends on

- [Directed Adjacency](../../directed-adjacency-2/part-01/directed-adjacency.md)
- [Balanced Edges](balanced-edges.md)
- [Semi Balanced Edges](semi-balanced-edges.md)
- [Edge List Of](edge-list-of.md)
- [Visit](visit.md)
- [Walk Edges](walk-edges.md)

## Proof depends on

- [Perm splice](perm-splice.md)
- [Walk Edges append](walk-edges-append.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.Graph.Hierholzer](../../../../../../../sources/v2/CSLibExt.md)
