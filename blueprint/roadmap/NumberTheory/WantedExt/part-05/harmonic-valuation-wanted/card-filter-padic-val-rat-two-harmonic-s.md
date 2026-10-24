---
declaration: theorem
origin: cited
statement: formalized
lean: MetaMathlibExt.card_filter_padicValRat_two_harmonic_sub
---

# Card filter padic Val Rat two harmonic sub

Fiber counts of the values `ν₂(H_n - H_m)`.

The extracted statement truncates the refinement locating these values in
the intervals determined by the partial sums `Mⱼ`; only the fiber counts
stated in the first part are formalized here. Verified computationally with
exact rational arithmetic for `n < 40`.

## Depends on

This node has no prerequisites.

## Sources

- [WantedExt, WantedExt.NumberTheory.HarmonicValuationWanted](../../../../../sources/v2/WantedExt.md)
- Lengyel, *On the 2-Adic Valuation of Differences of Harmonic Numbers*, INTEGERS 24 (2024), Article A27, Theorem 3 (`integers-2024-A27-thm-3`): writing `n = ∑_{i=1}^{t} 2^{aᵢ}` in binary, among the values `ν₂(H_n - H_m)` for `m = 0, 1, …, n - 1` exactly `2^{aᵢ}` are equal to `-aᵢ`, for each exponent `aᵢ` occurring in the expansion.
