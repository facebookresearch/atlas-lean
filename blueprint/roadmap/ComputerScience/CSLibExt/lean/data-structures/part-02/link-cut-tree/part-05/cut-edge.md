---
article_id: af_88db45ca2578aa80b55bda59
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.LinkCutTree.State.Valid.cutEdge
---

# Cut Edge

Edge cutting preserves the state invariant: on an adjacent pair it is
the composite of `makeRoot` and `cut`, and otherwise it only resets the
preferred path.

## Depends on

- [State](../part-03/state.md)
- [Valid](../part-03/valid.md)
- [Cut Edge](../part-04/cut-edge.md)

## Proof depends on

- [Tree](../../euler-tour-tree/part-01/tree.md)
- [Vertices](../../euler-tour-tree/part-01/vertices.md)
- [Parent Child](../part-02/parent-child.md)
- [Cut](../part-04/cut-2.md)
- [Make Root](../part-04/make-root-2.md)
- [Cut](../part-04/cut.md)
- [Make Root](../part-04/make-root.md)
- [Valid of preferred nil](../part-03/valid-of-preferred-nil.md)
- [Adjacent B](../part-01/adjacent-b.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.LinkCutTree](../../../../../../../../sources/v2/CSLibExt.md)
