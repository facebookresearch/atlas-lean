---
article_id: af_0788bf570bcbce8bf481f7b3
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.LinkCutTree.State.access_last
---

# Access last

After `access x` in a valid state, the root-to-`x` path of the tree
containing `x` is one of the preferred paths of the decomposition, and
`x` is its last (deepest) vertex: `p.getLast? = some x`. No auxiliary
splay tree is modeled, so no claim is made about a splay-tree root. This
is only the endpoint property of the accessed preferred path. Other
preferred paths off that root path are retained (`mem_preferred_access`).

## Depends on

- [Tree](../../euler-tour-tree/part-01/tree.md)
- [State](../part-03/state.md)
- [Mem](../part-03/mem.md)
- [Valid](../part-03/valid.md)
- [Access](access.md)
- [Paths](../part-03/paths.md)
- [Root Path](../part-02/root-path.md)

## Proof depends on

- [Children ind](../../euler-tour-tree/part-01/children-ind.md)
- [Vertices](../../euler-tour-tree/part-01/vertices.md)
- [Vertices node](../../euler-tour-tree/part-01/vertices-node.md)
- [Parent Child](../part-02/parent-child.md)
- [Decomp](../part-03/decomp.md)
- [Decomp fst eq root Path](../part-03/decomp-fst-eq-root-path.md)
- [Find Tree](../part-01/find-tree.md)
- [Get Last? root Path](../part-02/get-last-root-path.md)
- [Path Edges](../part-02/path-edges.md)
- [Tree Paths](../part-03/tree-paths.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.LinkCutTree](../../../../../../../../sources/v2/CSLibExt.md)
