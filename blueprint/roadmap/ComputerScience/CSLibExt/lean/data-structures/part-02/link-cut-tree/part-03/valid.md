---
article_id: af_e671f5c4144ef6bfdf81e547
declaration: def
origin: cited
statement: formalized
lean: Cslib.Algorithms.Lean.LinkCutTree.State.Valid
---

# Valid

The state invariant bundle used below: the vertex lists of the represented
trees are collectively duplicate-free (so the trees are vertex-disjoint), and
the preferred edges are a functional set of represented directed edges: no
duplicates, every preferred edge is a parent-child edge of some represented
tree, and each vertex has at most one preferred child. The duplicate-free
vertex condition also pins down the parent of each vertex, so the maximal
solid chains (`treePaths`) are genuine disjoint paths.

## Depends on

- [State](state.md)

## Proof depends on

- [Tree](../../euler-tour-tree/part-01/tree.md)
- [Vertices](../../euler-tour-tree/part-01/vertices.md)
- [Parent Child](../part-02/parent-child.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.LinkCutTree](../../../../../../../../sources/v2/CSLibExt.md)
