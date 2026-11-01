---
article_id: af_bd9b49d45dad53f5d4da3eb1
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.dresden_du_simplified_binet_of_initial_window
---

# Dresden du simplified binet of initial window

Strengthened simplified Binet formula with nearest-integer rounding for the integer-indexed
k-generalized Fibonacci sequence: `F n = ⌊c * α ^ (n - 1) + 1 / 2⌋` for
`n ≥ 2 - k`, under the finite initial condition `F n = 0` for `2 - k ≤ n < 1`, where `α`
is a positive root of
`x ^ k - x ^ (k-1) - ⋯ - 1` and `c = (α - 1) / (2 + (k + 1) * (α - 2))`.

Proof: We follow Dresden–Du's recurrence and first-crossing route, replacing their appeal to
the non-dominant-root results of Miles (1960) and Miller (1971) with an exact positive weighted
invariant.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.NumberTheory.Recurrences.DresdenDuSimplifiedBinet](../../../../../../../sources/v2/MathlibExt.md)
- G. P. B. Dresden and Z. Du, *A Simplified Binet Formula for k-Generalized Fibonacci Numbers*, Journal of Integer Sequences 17 (2014), Article 14.4.7, Theorem T2, lines 209-218, <https://cs.uwaterloo.ca/journals/JIS/VOL17/Dresden/dresden6.tex>.
