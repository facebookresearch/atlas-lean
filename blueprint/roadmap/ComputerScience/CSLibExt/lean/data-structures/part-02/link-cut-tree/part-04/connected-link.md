---
article_id: af_e2538916a6a61f9f17cf1bc5
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.LinkCutTree.State.connected_link
---

# Connected link

A link connects its endpoints: after `link x y`, `x` and `y` lie in one
represented tree. No invariant on the state is needed.

## Depends on

- [State](../part-03/state.md)
- [Connected](../part-03/connected.md)
- [Mem](../part-03/mem.md)
- [Link](link.md)

## Proof depends on

- [Tree](../../euler-tour-tree/part-01/tree.md)
- [Children ind](../../euler-tour-tree/part-01/children-ind.md)
- [Root](../../euler-tour-tree/part-01/root.md)
- [Vertices](../../euler-tour-tree/part-01/vertices.md)
- [Vertices node](../../euler-tour-tree/part-01/vertices-node.md)
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
