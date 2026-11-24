# Martingale CLT under the Lindeberg condition

For a martingale difference array (row `n`
has `n` increments, as in `LindebergConditionTriangular`) with square-integrable increments, if
the realized quadratic variation `∑_{k<n} X n k²` tends to `v` in probability and the Lindeberg
condition holds, the row sums converge in distribution to `N(0, v)`. The Lindeberg condition
implies McLeish's conditions (a) and (b), so this is a corollary of
`tendstoInDistribution_martingale_mcLeish`.

## Sources

- McLeish (1974), remarks following Theorem (2.3), pp. 621–622 (the Lindeberg condition implies (a) and (b)); compare P. Hall and C. C. Heyde, *Martingale Limit Theory and Its Application* (1980), Theorem 3.2.
