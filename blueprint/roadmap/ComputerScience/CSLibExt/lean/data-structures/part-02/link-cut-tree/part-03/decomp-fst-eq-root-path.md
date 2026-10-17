---
article_id: af_6ec2745e87b0d9dd6474b2ec
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.LinkCutTree.decomp_fst_eq_rootPath
---

# Decomp fst eq root Path

The downward path installed by the access edge update: when the edge
list `E` contains exactly the edges of the root-to-`x` path at vertices of
that path, the decomposition of the tree has that whole root path as its
downward preferred path.

## Depends on

- [Tree](../../euler-tour-tree/part-01/tree.md)
- [Vertices](../../euler-tour-tree/part-01/vertices.md)
- [Decomp](decomp.md)
- [Path Edges](../part-02/path-edges.md)
- [Root Path](../part-02/root-path.md)

## Proof depends on

- [Children ind](../../euler-tour-tree/part-01/children-ind.md)
- [Root](../../euler-tour-tree/part-01/root.md)
- [Vertices node](../../euler-tour-tree/part-01/vertices-node.md)
- [Get Last? root Path](../part-02/get-last-root-path.md)
- [Head? root Path](../part-02/head-root-path.md)
- [Nodup root Path](../part-02/nodup-root-path.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.LinkCutTree](../../../../../../../../sources/v2/CSLibExt.md)
