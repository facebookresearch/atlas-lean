# The oracle trend statistic is asymptotically χ²₁

Let `P` be a probability measure and `S_m = (G_m, Y_m)`, `m = 0, 1, 2, …`, independent and
identically distributed pairs of a genotype class `G_m ∈ {0, 1, 2}` and a case status `Y_m` under
`P`, with `S_0` measurable (multinomial sampling of the `2 × 3` table: the numbers of cases and
controls are random). Suppose the null hypothesis that `G_0` and `Y_0` are independent, that the
case probability `p = P(Y_0 = true)` satisfies `0 < p < 1`, and that the score `G_0` has positive
variance (at least two genotype classes have positive probability). Write `x_m = G_m` for the
genotype score and `c_m` for the [case indicator](case-ind.md) of subject `m`, so that `E[c_0] = p`
and `Var(c_0) = p (1 − p)`. Then the oracle statistic, with the null parameters known instead of
estimated,

`T*_N = (N^(−1/2) ∑_{m<N} (x_m − E[x_0]) (c_m − E[c_0]))² / (Var(x_0) Var(c_0))`,

converges in distribution under `P`, as `N → ∞`, to the
[χ² law with one degree of freedom](../../../../Probability/distributions/continuous/chi-square-distribution/chi-square-measure.md),
the same limit as the [estimated statistic](tendsto-in-distribution-ca-stat.md). For `N = 0` the
factor `N^(−1/2)` is taken to be `0`.
