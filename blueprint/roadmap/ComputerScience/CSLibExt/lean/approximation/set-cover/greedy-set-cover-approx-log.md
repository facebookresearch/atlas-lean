---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.TimeM.greedySetCover_approx_log
---

# Greedy Set Cover approx log

CLRS Corollary 35.5: greedy set cover is an `(ln |U| + 1)`-approximation, via Mathlib's
`harmonic_le_one_add_log`.

## Depends on

- [Greedy Set Cover](greedy-set-cover.md)

## Proof depends on

- [Greedy Set Cover approx card](greedy-set-cover-approx-card.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.Approximation.SetCover](../../../../../../sources/v2/CSLibExt.md)
