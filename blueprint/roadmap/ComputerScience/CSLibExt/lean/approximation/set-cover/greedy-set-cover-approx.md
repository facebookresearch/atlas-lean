---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.TimeM.greedySetCover_approx
---

# Greedy Set Cover approx

CLRS Theorem 35.4: if every set of `F` has at most `d` elements, the greedy cover of `U` has
at most `H(d)` times as many sets as any cover of `U` drawn from `F`.

## Depends on

- [Greedy Set Cover](greedy-set-cover.md)

## Proof depends on

- [Greedy Set Cover length le sum harmonic](greedy-set-cover-length-le-sum-harmonic.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.Approximation.SetCover](../../../../../../sources/v2/CSLibExt.md)
