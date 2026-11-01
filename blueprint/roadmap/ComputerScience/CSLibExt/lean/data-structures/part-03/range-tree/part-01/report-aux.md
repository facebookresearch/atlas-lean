---
article_id: af_be25ee957833da5b0ff7abf2
declaration: def
origin: cited
statement: formalized
lean: Cslib.Algorithms.Lean.RangeTree.reportAux
---

# Report Aux

Accumulator range report for `[lo, hi]`: a node whose cached interval is
disjoint from the query contributes nothing, a node contained in it
contributes its whole leaf list onto the accumulator (the canonical-node
case, via the linear `toListAux`), and otherwise both children are
searched. The cached bounds make each pruning test constant-time.

## Depends on

- [Range Tree](range-tree.md)

## Proof depends on

- [To List Aux](to-list-aux.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.RangeTree](../../../../../../../../sources/v2/CSLibExt.md)
