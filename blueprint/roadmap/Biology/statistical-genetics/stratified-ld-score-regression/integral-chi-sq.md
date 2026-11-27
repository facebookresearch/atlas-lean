# Expected statistic with per-marker variances

For every [stratified LD-score model](model.md) on a measure $\mu$, every real $N \times M$ genotype matrix $X$ and every marker $j$,

$$\int \chi^2_j \, d\mu = N \sum_{k=1}^{M} r_{jk}^2\, \sigma^2_k + \frac{\sigma^2_e}{N} \sum_{i=1}^{N} X_{ij}^2, \qquad r_{jk} = \frac{1}{N} \sum_{i=1}^{N} X_{ij} X_{ik},$$

where $\chi^2_j$ is the [association statistic](chi-sq.md), with the convention $x/0 = 0$ (for $N = 0$ both sides are $0$).
