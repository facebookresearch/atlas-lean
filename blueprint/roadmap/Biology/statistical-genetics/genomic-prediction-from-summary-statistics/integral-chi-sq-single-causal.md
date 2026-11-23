# Expected association statistic with one causal variant

Let a [stratified LD-score model](stratified-model.md) on a measure $\mu$ have $N \ne 0$ individuals, noise variance $\sigma_e^2$ and a single category, whose marker set is $\{c\}$ and whose contribution is $\tau$. Let $X$ be a real $N \times M$ genotype matrix that is standardized (every column has sum $0$ and sum of squares $N$). Then for every marker $j$ (Pritchard & Przeworski 2001),

$$\int \chi^2_j \, d\mu = N \tau\, r_{jc}^2 + \sigma_e^2, \qquad r_{jc} = \frac{1}{N} \sum_{i=1}^{N} X_{ij} X_{ic},$$

where $\chi^2_j$ is the [association statistic](chi-sq.md). When $\mu$ is a probability measure, it is the expected association statistic of a marker in linkage disequilibrium with a single causal variant: the noise level $\sigma_e^2$ plus $N\tau\, r_{jc}^2$. In general $\sigma_e^2$ is a raw second moment of the noise, and a variance only for centred noise under a probability measure.

## Sources

- J. K. Pritchard, M. Przeworski, *Linkage disequilibrium in humans: models and data*, Am. J. Hum. Genet. 69 (2001), 1–14.
