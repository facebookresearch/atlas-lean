---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.TimeM.weightedGreedySetCover_cost_le_sum_harmonic
---

# The potential bound

**The potential bound.** With nonnegative costs, for every cover `C*` of `U` drawn from `F`,
the greedy cover costs at most `∑_{S ∈ C*} w S · H(|S ∩ U|)`.

## Depends on

- [Total Cost](total-cost.md)
- [Weighted Greedy Set Cover](weighted-greedy-set-cover.md)

## Proof depends on

- [Best Ratio Set](best-ratio-set.md)
- [Card le sum card inter](../set-cover/card-le-sum-card-inter.md)
- [Div le harmonic sub](../set-cover/div-le-harmonic-sub.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.Approximation.WeightedSetCover](../../../../../../sources/v2/CSLibExt.md)
