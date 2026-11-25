# Expected chi-squared statistic of a standardized marker

Let a [stratified LD-score model](model.md) on a measure $\mu$ have $N \ne 0$ individuals, and let $X$ be a [standardized](../ld-score-regression/is-standardized.md) real $N \times M$ genotype matrix (every column has sum $0$ and sum of squares $N$). Then for every marker $j$,

$$\int \chi^2_j \, d\mu = N \sum_{k=1}^{M} r_{jk}^2\, \sigma^2_k + \sigma^2_e,$$

where $\chi^2_j$ is the [association statistic](chi-sq.md) and $r_{jk} = \frac1N \sum_i X_{ij} X_{ik}$.
