---
article_id: af_c606e2a6b6d448bccae0f00e
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.LinkCutTree.State.Valid.cut
---

# Cut

Cutting preserves the state invariant: pruning partitions the cut
tree's vertex list into remainder plus detached subtree up to permutation
(`perm_vertices_pruneAt`), the rest of the forest is untouched, and the
preferred edges are reset.

## Depends on

- [State](../part-03/state.md)
- [Valid](../part-03/valid.md)
- [Cut](cut.md)

## Proof depends on

- [Tree](../../euler-tour-tree/part-01/tree.md)
- [Vertices](../../euler-tour-tree/part-01/vertices.md)
- [Parent Child](../part-02/parent-child.md)
- [Valid of preferred nil](../part-03/valid-of-preferred-nil.md)
- [Find Subtree](../part-01/find-subtree.md)
- [Find Tree](../part-01/find-tree.md)
- [Perm flat Map remove Tree](../part-01/perm-flat-map-remove-tree.md)
- [Perm vertices prune At](../part-02/perm-vertices-prune-at.md)
- [Prune At](../part-02/prune-at.md)
- [Remove Tree](../part-01/remove-tree.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.LinkCutTree](../../../../../../../../sources/v2/CSLibExt.md)
