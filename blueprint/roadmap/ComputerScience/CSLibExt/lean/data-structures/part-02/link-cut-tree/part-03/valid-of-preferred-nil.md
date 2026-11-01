---
article_id: af_91b4691c792d2aa49c477ebd
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.LinkCutTree.State.valid_of_preferred_nil
---

# Valid of preferred nil

A state with no preferred edges is valid exactly when its forest is
duplicate-free. This is the invariant after every structural operation,
which resets all edges to dashed.

## Depends on

- [Tree](../../euler-tour-tree/part-01/tree.md)
- [Vertices](../../euler-tour-tree/part-01/vertices.md)
- [State](state.md)
- [Valid](valid.md)

## Proof depends on

- [Parent Child](../part-02/parent-child.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.LinkCutTree](../../../../../../../../sources/v2/CSLibExt.md)
