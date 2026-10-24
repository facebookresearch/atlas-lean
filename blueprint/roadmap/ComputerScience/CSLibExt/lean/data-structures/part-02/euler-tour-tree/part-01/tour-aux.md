---
article_id: af_404ba7c0aebdd9fa40886492
declaration: def
origin: cited
statement: formalized
lean: Cslib.Algorithms.Lean.EulerTourTree.Tree.tourAux
---

# Tour Aux

Accumulator Euler tour: `tourAux t acc = tour t ++ acc` (see
`tourAux_eq`), so `tour` is linear rather than repeatedly appending child
tours.

## Depends on

- [Tree](tree.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.EulerTourTree](../../../../../../../../sources/v2/CSLibExt.md)
