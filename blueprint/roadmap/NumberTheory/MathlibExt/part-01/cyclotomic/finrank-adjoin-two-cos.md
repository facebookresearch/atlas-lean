---
article_id: af_86187933489bcb86259b3f0f
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.finrank_adjoin_two_cos
---

# Two Cos Algebraic Degree

The degree over `ℚ` of `2 * cos (2 * π * k / n)` is `φ(n) / 2`: the algebraic core
of the Gauss–Wantzel constructibility criterion (straightedge-and-compass
constructibility has no Mathlib predicate).

The source states that `2cos(2kπ/n)` with `1 ≤ k ≤ n` and `gcd(k,n) = 1` is an
algebraic integer of degree `φ(n)/2`; the formalization renders the degree as the
`finrank` of the adjunction. The theorem drops the range `1 ≤ k ≤ n` and holds
for every natural `k` coprime to `n`, since the cosine depends only on `k` modulo
`n`. The same source fact is stated via `realCyclotomicPolynomial` by
`MetaMathlibExt.natDegree_realCyclotomicPolynomial` and the still-open `Wanted`
entry `realCyclotomicPolynomial_eq_minpoly_two_cos_of_coprime`; this module is the
direct `finrank` formulation.
Proves `Wanted` entry `finrank_adjoin_two_cos`.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.NumberTheory.Cyclotomic.TwoCosAlgebraicDegree](../../../../../sources/v2/MathlibExt.md)
- Pinthira Tangsupphathawat and Vichian Laohakosol, "Minimal Polynomials of Algebraic Cosine Values at Rational Multiples of π," Journal of Integer Sequences 19 (2016), Article 16.2.8, Lehmer's theorem recalled in the Introduction (equation label lehmer), lines 83–90, https://cs.uwaterloo.ca/journals/JIS/VOL19/Laohakosol/lao2.tex
