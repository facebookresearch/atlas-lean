---
article_id: af_b6ac2877eb826929534390f4
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.dirichlet_series_gcd_sum
---

# Gcd Sum Dirichlet

Dirichlet series of the gcd-sum `g(n) = ∑_{i=1}^n gcd(n,i)`: for `2 < s.re`,
the series `∑ g(n)/n^s` equals `ζ(s-1)^2/ζ(s)`.

The source writes `g` as the Dirichlet convolution of `id` with `φ`,
giving `ζ(s-1) · (ζ(s-1)/ζ(s))`; the convolution identity
`g(n) = ∑_{d|n} d * φ(n/d)` was checked for `n = 1..200`, and partial
sums at `s = 3` converge toward `ζ(2)^2/ζ(3)` as expected.
Proves `Wanted` entry `dirichlet_series_gcd_sum`.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.NumberTheory.ArithmeticFunction.GcdSumDirichlet](../../../../../sources/v2/MathlibExt.md)
- Kevin A. Broughan, "The gcd-sum function," Journal of Integer Sequences 4 (2001), Article 01.2.2, Theorem (unlabeled), equations (labels 12, 8), lines 336–349, https://cs.uwaterloo.ca/journals/JIS/VOL4/BROUGHAN/gcdsum.tex
