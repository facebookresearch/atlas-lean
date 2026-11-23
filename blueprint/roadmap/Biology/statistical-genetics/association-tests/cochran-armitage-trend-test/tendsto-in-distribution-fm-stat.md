# Fixed-margin Cochran–Armitage test is asymptotically χ²₁

Let `P` be a probability measure and, for each `N ∈ ℕ`, `R_N ≤ N` a number of cases and `G_{N,k}`,
`k ∈ ℕ`, measurable random genotype classes in `{0, 1, 2}` such that `G_{N,0}, …, G_{N,N−1}` are
independent under `P`. The cases `k < R_N` have genotype law `π_case` and the controls `R_N ≤ k < N`
have genotype law `π_ctrl` (product-binomial sampling: the numbers of cases and controls are fixed,
not random; designs of different sizes need not share subjects). Suppose the null hypothesis
`π_case = π_ctrl`, that the genotype score has positive variance under `π_case`, and that `R_N → ∞`
and `N − R_N → ∞`. Then the [fixed-margin statistic](fm-stat.md) `T(R_N, N, G_{N,·})` converges in
distribution under `P`, as `N → ∞`, to the
[χ² law with one degree of freedom](../../../../Probability/distributions/continuous/chi-square-distribution/chi-square-measure.md).

No condition on the case fraction `R_N / N` is needed: it may oscillate or tend to `0` or `1`.
Measurability is assumed for every `G_{N,k}`, also for the entries `k ≥ N` that the statistic does
not read.

## Sources

- P. Armitage, *Tests for linear trends in proportions and frequencies*, Biometrics 11 (1955),
  375–386.
- P. Billingsley, *Probability and Measure*, 3rd ed., Wiley (1995), Theorem 27.2.
