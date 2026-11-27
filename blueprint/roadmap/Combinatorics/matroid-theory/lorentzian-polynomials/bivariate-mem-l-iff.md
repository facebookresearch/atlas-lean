# Bivariate Lorentzian polynomials

Write a bivariate form of degree $d$ as $f = \sum_{k=0}^{d} a_k w_1^k w_2^{d-k}$. Then $f$ is
Lorentzian if and only if the sequence $a_0, \dots, a_d$

- is nonnegative,
- is *ultra log-concave*: $\frac{a_k^2}{\binom{d}{k}^2} \ge \frac{a_{k-1}}{\binom{d}{k-1}} \cdot \frac{a_{k+1}}{\binom{d}{k+1}}$ for $0 < k < d$,
- and has no internal zeros: $a_{k_1} a_{k_3} > 0$ implies $a_{k_2} > 0$ whenever
  $k_1 < k_2 < k_3 \le d$.

This is Brändén and Huh's Example 2.26. It is the bridge from Lorentzian polynomials to
inequalities between numbers: specialising a Lorentzian polynomial to two variables by a
nonnegative substitution produces an ultra log-concave sequence. For a real-rooted polynomial
with nonnegative coefficients the same conclusion is Newton's inequality, the stable case.

## Informally uses

- [Lorentzian polynomials as the closure of strictly Lorentzian polynomials](theorem-2-25.md):
  the example combines the computation of Example 2.3 (a bivariate form with positive
  coefficients is strictly Lorentzian if and only if its coefficients are strictly ultra
  log-concave) with Theorem 2.25.

## Background

- [Positive sequences satisfying Newton's inequalities are unimodal](../../permutations/permutation-statistics/fixed-points-of-permutations-with-k-cycles/unimodal-of-newton-inequalities.md):
  the ultra log-concavity inequalities above, for positive sequences, imply unimodality.

## Sources

- P. Brändén and J. Huh, *Lorentzian polynomials*, Ann. of Math. 192 (2020), 821–891,
  Example 2.3, Theorem 2.25 and Example 2.26, https://arxiv.org/abs/1902.03719.
