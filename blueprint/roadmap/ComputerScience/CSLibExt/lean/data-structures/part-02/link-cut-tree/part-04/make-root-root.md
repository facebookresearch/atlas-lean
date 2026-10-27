---
article_id: af_6a50caf90b2947a11a3c8480
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.LinkCutTree.State.makeRoot_root
---

# Make Root root

After `makeRoot x`, some represented tree is rooted at `x` and has `x`
as a vertex: the rerooted old tree of `x`.

## Depends on

- [Tree](../../euler-tour-tree/part-01/tree.md)
- [Root](../../euler-tour-tree/part-01/root.md)
- [Vertices](../../euler-tour-tree/part-01/vertices.md)
- [State](../part-03/state.md)
- [Mem](../part-03/mem.md)
- [Make Root](make-root.md)

## Proof depends on

- [Children ind](../../euler-tour-tree/part-01/children-ind.md)
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
