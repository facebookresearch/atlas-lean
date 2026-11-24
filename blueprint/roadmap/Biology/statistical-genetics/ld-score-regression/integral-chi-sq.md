# Expected association statistic for an arbitrary genotype matrix

For every [LD-score model](model.md) on a measure $\mu$ with heritability $h^2$, every real $N \times M$ genotype matrix $X$ and every marker $j$,

$$\int \chi^2_j \, d\mu = \frac{N h^2}{M}\, \ell_j + \frac{1 - h^2}{N} \sum_{i=1}^{N} X_{ij}^2,$$

where $\chi^2_j$ is the [association statistic](chi-sq.md) and $\ell_j$ the [LD score](ld-score.md), with the convention $x/0 = 0$ (for $N = 0$ both sides are $0$).
