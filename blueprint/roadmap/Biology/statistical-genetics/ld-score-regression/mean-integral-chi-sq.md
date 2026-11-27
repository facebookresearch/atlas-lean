# Polygenic inflation of the mean association statistic

Let an [LD-score model](model.md) on a measure $\mu$ have heritability $h^2$, $N \ne 0$ individuals and $M \ne 0$ markers, and let $X$ be a [standardized](is-standardized.md) real $N \times M$ genotype matrix. Then

$$\frac{1}{M} \sum_{j=1}^{M} \int \chi^2_j \, d\mu = 1 - h^2 + \frac{N h^2}{M}\, \bar\ell,$$

where $\chi^2_j$ is the [association statistic](chi-sq.md) and $\bar\ell$ the [mean LD score](mean-ldscore.md).
