---
article_id: af_d07847c3452b38cd35536186
declaration: def
origin: cited
statement: formalized
lean: Cslib.Algorithms.Lean.LinkCutTree.adjacentB
---

# Adjacent B

Computable adjacency test: `adjacentB a b t = true` exactly when
`Adjacent a b t` (`adjacentB_eq_true_iff`). This is the guard evaluated by
`State.cutEdge` before it cuts.

## Depends on

- [Tree](../../euler-tour-tree/part-01/tree.md)

## Proof depends on

- [Root](../../euler-tour-tree/part-01/root.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.LinkCutTree](../../../../../../../../sources/v2/CSLibExt.md)
