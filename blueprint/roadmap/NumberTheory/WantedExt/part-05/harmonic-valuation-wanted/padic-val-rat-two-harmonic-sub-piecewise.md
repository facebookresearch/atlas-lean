---
declaration: theorem
origin: cited
statement: formalized
lean: MetaMathlibExt.padicValRat_two_harmonic_sub_piecewise
---

# Padic Val Rat two harmonic sub piecewise

Piecewise valuation formula.

The accompanying lower bound (3.2) is garbled in the extraction and is not
formalized. Both branches were verified computationally with exact rational
arithmetic for `m < 20`, `n < 45`.

## Depends on

This node has no prerequisites.

## Sources

- [WantedExt, WantedExt.NumberTheory.HarmonicValuationWanted](../../../../../sources/v2/WantedExt.md)
- Lengyel, *On the 2-Adic Valuation of Differences of Harmonic Numbers*, INTEGERS 24 (2024), Article A27, Theorem 6, formula (3.1) (`integers-2024-A27-thm-6`): let `M = ⌈log₂(m + 1)⌉` and `j = ⌊(n - m) / 2^M⌋`, where `1 ≤ m ≤ n`. Then `ν₂(H_n - H_{n-m}) = -M + 1` when `2^M * j + m ≤ n ≤ 2^M * (j + 1) - 1`, and `ν₂(H_n - H_{n-m}) = -M - ν₂(j + 1)` when `2^M * (j + 1) ≤ n ≤ 2^M * (j + 1) + m - 1`.
