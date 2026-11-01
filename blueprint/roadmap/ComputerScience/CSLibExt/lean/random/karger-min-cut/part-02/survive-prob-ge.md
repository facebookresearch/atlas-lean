---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.Karger.surviveProb_ge
---

# Each minimum cut survives with probability at least `2 / (n (n - 1))`

**Each minimum cut survives with probability at least `2 / (n (n - 1))`** (on a connected
multigraph, minimum cut size `k ≥ 1`): the run outputs that particular cut.

## Depends on

- [Is Cut](../part-01/is-cut.md)
- [Is Min Cut](../part-01/is-min-cut.md)
- [State](../part-01/state.md)
- [Valid](../part-01/valid.md)
- [Cut Size](../part-01/cut-size.md)
- [Survive Prob](survive-prob.md)

## Proof depends on

- [Card mul le two mul edges](../part-01/card-mul-le-two-mul-edges.md)
- [Contract](../part-01/contract.md)
- [Cut Size contract](../part-01/cut-size-contract.md)
- [Is Min Cut contract](../part-01/is-min-cut-contract.md)
- [Rename](../part-01/rename.md)
- [Valid contract](../part-01/valid-contract.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.Random.KargerMinCut](../../../../../../../sources/v2/CSLibExt.md)
