---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.TimeM.greedySetCover_length_le_sum_harmonic
---

# Greedy Set Cover length le sum harmonic

The potential bound: for every cover `C*` of `U` drawn from `F`, the greedy cover has at most
`∑_{S ∈ C*} H(|S ∩ U|)` sets.

## Depends on

- [Greedy Set Cover](greedy-set-cover.md)

## Proof depends on

- [Best Set](best-set.md)
- [Card le sum card inter](card-le-sum-card-inter.md)
- [Div le harmonic sub](div-le-harmonic-sub.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.Approximation.SetCover](../../../../../../sources/v2/CSLibExt.md)
