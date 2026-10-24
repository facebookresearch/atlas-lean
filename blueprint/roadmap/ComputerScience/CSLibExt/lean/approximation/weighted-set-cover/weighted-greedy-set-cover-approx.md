---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.TimeM.weightedGreedySetCover_approx
---

# Chvátal's bound

**Chvátal's bound.** With nonnegative costs, if every set of `F` has at most `d` elements, the
greedy cover of `U` costs at most `H(d)` times any cover of `U` drawn from `F`.

## Depends on

- [Total Cost](total-cost.md)
- [Weighted Greedy Set Cover](weighted-greedy-set-cover.md)

## Proof depends on

- [The potential bound](weighted-greedy-set-cover-cost-le-sum-ha.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.Approximation.WeightedSetCover](../../../../../../sources/v2/CSLibExt.md)
