# Expected statistic under stratification for standardized genotypes

Let an [LD-score model](model.md) with heritability $h^2$ and $N \ne 0$ individuals be defined on a probability measure $\mu$, with $\int \beta_k \, d\mu = 0$ and $\int \varepsilon_i \, d\mu = 0$ for all $k$ and $i$, and let $X$ be a [standardized](is-standardized.md) real $N \times M$ genotype matrix. Then for every $s \in \mathbb{R}$, $c \in \mathbb{R}^N$ and every marker $j$,

$$\int \chi^2_j \, d\mu = \frac{N h^2}{M}\, \ell_j + (1 - h^2) + N s^2 \Bigl(\frac{1}{N} \sum_{i=1}^{N} X_{ij} c_i\Bigr)^2,$$

where $\chi^2_j$ is the [association statistic under stratification](chi-sq-strat.md) and $\ell_j$ the [LD score](ld-score.md), with the convention $x/0 = 0$ when $M = 0$.
