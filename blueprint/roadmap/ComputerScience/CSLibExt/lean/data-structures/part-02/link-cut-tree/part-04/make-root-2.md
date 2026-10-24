---
article_id: af_0c26a786707a779b7495cb02
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.LinkCutTree.State.Valid.makeRoot
---

# Make Root

Rerooting preserves the state invariant: the new forest has the same
flat vertex list as the old one up to permutation (the rerooted tree
replaces its original), and the preferred edges are reset.

## Depends on

- [State](../part-03/state.md)
- [Valid](../part-03/valid.md)
- [Make Root](make-root.md)

## Proof depends on

- [Tree](../../euler-tour-tree/part-01/tree.md)
- [Vertices](../../euler-tour-tree/part-01/vertices.md)
- [Parent Child](../part-02/parent-child.md)
- [Valid of preferred nil](../part-03/valid-of-preferred-nil.md)
- [Find Tree](../part-01/find-tree.md)
- [Perm flat Map remove Tree](../part-01/perm-flat-map-remove-tree.md)
- [Perm vertices reroot At](../part-02/perm-vertices-reroot-at.md)
- [Remove Tree](../part-01/remove-tree.md)
- [Reroot At](../part-01/reroot-at.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.LinkCutTree](../../../../../../../../sources/v2/CSLibExt.md)
