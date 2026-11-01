---
article_id: af_9709e634fb03996416a95b0c
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.LinkCutTree.State.Valid.link
---

# Link

Linking preserves the state invariant: the joined tree has the union
of the two old vertex lists up to permutation (rerooting and grafting both
permute), the rest of the forest is untouched, and the preferred path is
reset.

## Depends on

- [State](../part-03/state.md)
- [Valid](../part-03/valid.md)
- [Link](link.md)

## Proof depends on

- [Tree](../../euler-tour-tree/part-01/tree.md)
- [Vertices](../../euler-tour-tree/part-01/vertices.md)
- [Parent Child](../part-02/parent-child.md)
- [Valid of preferred nil](../part-03/valid-of-preferred-nil.md)
- [Find Tree](../part-01/find-tree.md)
- [Graft At](../part-01/graft-at.md)
- [Perm flat Map remove Tree](../part-01/perm-flat-map-remove-tree.md)
- [Perm vertices graft At](../part-01/perm-vertices-graft-at.md)
- [Perm vertices reroot At](../part-02/perm-vertices-reroot-at.md)
- [Remove Tree](../part-01/remove-tree.md)
- [Reroot At](../part-01/reroot-at.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.LinkCutTree](../../../../../../../../sources/v2/CSLibExt.md)
