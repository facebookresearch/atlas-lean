# Singular multinomial design: no χ²₁ limit

Let `P` be a probability measure and `S_m = (G_m, Y_m)` subjects that all have the same law as `S_0`
under `P`. If `G_0 = g` almost surely for one genotype class `g`, then the
[Cochran–Armitage statistic](ca-stat.md) of the first `N` subjects does not converge in distribution
to the
[χ² law with one degree of freedom](../../../../Probability/distributions/continuous/chi-square-distribution/chi-square-measure.md):
it is [almost surely `0` for every `N`](ca-stat-ae-eq-zero-of-genotype-const.md), so its limit law
is the point mass at `0`. The hypothesis of positive score variance in the
[asymptotic theorem](tendsto-in-distribution-ca-stat.md) cannot be dropped.
