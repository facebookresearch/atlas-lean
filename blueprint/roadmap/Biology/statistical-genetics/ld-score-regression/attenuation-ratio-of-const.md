# Attenuation ratio under constant stratification

Let an [LD-score model](model.md) with heritability $h^2$, $N \ne 0$ individuals and $M \ne 0$ markers be defined on a probability measure $\mu$, with $\int \beta_k \, d\mu = 0$ and $\int \varepsilon_i \, d\mu = 0$ for all $k$ and $i$, and let $X$ be a [standardized](is-standardized.md) real $N \times M$ genotype matrix. Let $s \in \mathbb{R}$, $c \in \mathbb{R}^N$ and $a \in \mathbb{R}$ satisfy $s^2 \bigl(\frac1N \sum_i X_{ij} c_i\bigr)^2 = a$ for every marker $j$, and let $\bar\chi^2 = \frac1M \sum_j \int \chi^2_j \, d\mu$ be the mean expected [association statistic under stratification](chi-sq-strat.md). Then the [attenuation ratio](attenuation-ratio.md) of the intercept $1 - h^2 + Na$ and $\bar\chi^2$ is

$$R(1 - h^2 + Na,\ \bar\chi^2) = \frac{N a - h^2}{N h^2 \bar\ell / M + N a - h^2},$$

where $\bar\ell$ is the [mean LD score](mean-ldscore.md), with the convention $x/0 = 0$.
