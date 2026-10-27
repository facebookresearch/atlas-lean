---
article_id: af_96fab6bc96abf8102dc2979b
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.LinkCutTree.State.connected_makeRoot
---

# Connected make Root

`makeRoot x` keeps `x` connected to exactly the vertices it was
connected to: rerooting spans the same vertex set as the old tree (and,
by `rerootAt`, the same undirected edges). Vertex disjointness is the
side condition that pins down which tree that is.

## Depends on

- [State](../part-03/state.md)
- [Connected](../part-03/connected.md)
- [Valid](../part-03/valid.md)
- [Make Root](make-root.md)

## Proof depends on

- [Tree](../../euler-tour-tree/part-01/tree.md)
- [Children ind](../../euler-tour-tree/part-01/children-ind.md)
- [Root](../../euler-tour-tree/part-01/root.md)
- [Vertices](../../euler-tour-tree/part-01/vertices.md)
- [Vertices node](../../euler-tour-tree/part-01/vertices-node.md)
- [Parent Child](../part-02/parent-child.md)
- [Mem](../part-03/mem.md)
- [Find Tree](../part-01/find-tree.md)
- [Graft At](../part-01/graft-at.md)
- [Mem vertices graft At](../part-01/mem-vertices-graft-at.md)
- [Mem vertices reroot At](../part-01/mem-vertices-reroot-at.md)
- [Remove Tree](../part-01/remove-tree.md)
- [Reroot At](../part-01/reroot-at.md)
- [Reroot At eq none of not mem](../part-01/reroot-at-eq-none-of-not-mem.md)
- [Root graft At](../part-01/root-graft-at.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.LinkCutTree](../../../../../../../../sources/v2/CSLibExt.md)
