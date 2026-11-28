# The Cochran–Armitage trend test is asymptotically χ²₁

Let `P` be a probability measure and `S_m = (G_m, Y_m)`, `m = 0, 1, 2, …`, independent and
identically distributed pairs of a genotype class `G_m ∈ {0, 1, 2}` and a case status `Y_m` under
`P`, with `S_0` measurable (multinomial sampling of the `2 × 3` table: the numbers of cases and
controls are random). Suppose the null hypothesis that `G_0` and `Y_0` are independent, that the
case probability `p = P(Y_0 = true)` satisfies `0 < p < 1`, and that the score `G_0` has positive
variance (at least two genotype classes have positive probability). Then the
[Cochran–Armitage statistic](ca-stat.md) `T_N` of the first `N` subjects converges in distribution
under `P`, as `N → ∞`, to the
[χ² law with one degree of freedom](../../../../Probability/distributions/continuous/chi-square-distribution/chi-square-measure.md).

The case probability and the genotype frequencies are estimated from the data inside `T_N`; the
limit still has one degree of freedom. The case–control design that fixes the numbers of cases and
controls is treated in [the fixed-margin theorem](tendsto-in-distribution-fm-stat.md).

## Sources

- W. G. Cochran, *Some methods for strengthening the common χ² tests*, Biometrics 10 (1954),
  417–451.
- P. Armitage, *Tests for linear trends in proportions and frequencies*, Biometrics 11 (1955),
  375–386.
