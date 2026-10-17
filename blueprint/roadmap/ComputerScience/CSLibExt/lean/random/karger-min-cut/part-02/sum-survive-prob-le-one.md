---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.Karger.sum_surviveProb_le_one
---

# The survival events of distinct cuts are disjoint

**The survival events of distinct cuts are disjoint**: a run outputs at most one partition, so
the survival probabilities of pairwise distinct cuts add up to at most `1`.

## Depends on

- [Distinct On](distinct-on.md)
- [State](../part-01/state.md)
- [Valid](../part-01/valid.md)
- [Survive Prob](survive-prob.md)

## Proof depends on

- [Is Cut](../part-01/is-cut.md)
- [Contract](../part-01/contract.md)
- [Rename](../part-01/rename.md)
- [Valid contract](../part-01/valid-contract.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.Random.KargerMinCut](../../../../../../../sources/v2/CSLibExt.md)
