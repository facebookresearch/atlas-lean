---
declaration: theorem
origin: cited
statement: formalized
lean: MetaMathlibExt.sum_padicValRat_two_harmonic_sub
---

# Sum padic Val Rat two harmonic sub

Sum of valuations over all `m < n`.

The extracted statement flattens the displayed aggregation over `m`; the sum
reading used here (rather than a product of valuations) was verified
computationally with exact rational arithmetic for `n ≤ 16`.

## Depends on

This node has no prerequisites.

## Sources

- [WantedExt, WantedExt.NumberTheory.HarmonicValuationWanted](../../../../../sources/v2/WantedExt.md)
- Lengyel, *On the 2-Adic Valuation of Differences of Harmonic Numbers*, INTEGERS 24 (2024), Article A27, Corollary 2 (`integers-2024-A27-cor-2`): `∑_{m=0}^{n-1} ν₂(H_n - H_m) = -a(n)`, where `a(n) = weightedBinaryDigitSum n`.
