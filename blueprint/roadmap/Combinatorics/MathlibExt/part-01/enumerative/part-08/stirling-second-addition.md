---
article_id: af_3bf5345deaccbfafe5eb4ae5
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.stirlingSecond_addition
---

# Stirling Second Addition

Addition formula for the Stirling numbers of the second kind.

The source sums `n = 1, …, k` and `m = k - n, …, v`, matching the
`Finset.Icc` ranges below.

The hypothesis `0 < u` is not explicit in the source, but this encoding needs it: at
`(u, v, k) = (0, 1, 1)` the left side is `1`, while the sum over `n ∈ Finset.Icc 1 1` is `0`
because `Nat.stirlingSecond 0 1 = 0`.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.Combinatorics.Enumerative.StirlingSecondAddition](../../../../../../sources/v2/MathlibExt.md)
- Grzegorz Rządkowski, "Two Formulas for Successive Derivatives and Their Applications," Journal of Integer Sequences 12 (2009), Article 09.8.2, Theorem, equation (ex33), lines 198–204, https://cs.uwaterloo.ca/journals/JIS/VOL12/Rzadkowski/rzadkowski3.tex
