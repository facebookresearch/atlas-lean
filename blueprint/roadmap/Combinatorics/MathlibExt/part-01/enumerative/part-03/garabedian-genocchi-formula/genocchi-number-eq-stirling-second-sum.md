---
article_id: af_23ff033158a9dfe8b5de5666
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.genocchiNumber_eq_stirlingSecond_sum
---

# Genocchi Number eq stirling Second sum

Garabedian's explicit formula for the Genocchi numbers: for `n ≥ 1`,
`G n = n * ∑ k = 1..n, (-1)^(n-k) * (k-1)! * S(n, k) / 2^(k-1)`,
where the left-hand side uses the canonical generating-function definition
`genocchiNumber`; the source identifies that same sequence with its Bernoulli
formula, exactly the first equality in the source's displayed formula (g19).

Historical attribution: H. L. Garabedian, "A new formula for the Bernoulli
numbers," Bulletin of the American Mathematical Society 46 (1940), 531–533,
DOI `10.1090/S0002-9904-1940-07255-6`.

Since `k ∈ Finset.Icc 1 n`, both natural subtractions `n - k` and `k - 1`
are genuine differences. It follows from `genocchiNumber_eq_stirlingSecond_sum_general`; the
hypothesis `hn` is unused and keeps the source's shape.

## Depends on

- [Genocchi Number](../../../../../../NumberTheory/MathlibExt/part-06/genocchi-number/genocchi-number.md)

## Proof depends on

- [Genocchi Number eq stirling Second sum general](genocchi-number-eq-stirling-second-sum-g.md)

## Sources

- [MathlibExt, MathlibExt.Combinatorics.Enumerative.GarabedianGenocchiFormula](../../../../../../../sources/v2/MathlibExt.md)
- Schehrazade Zerroukhat and Laala Khaldi, "A Note on Explicit Formulas for Bernoulli and Genocchi Numbers," Journal of Integer Sequences 28 (2025), Article 25.6.7, lines 184–194 of the official TeX: <https://cs.uwaterloo.ca/journals/JIS/VOL28/Zerroukhat/zerrou3.tex>.
