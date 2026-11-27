# Expected association statistic under stratification

Let an [LD-score model](model.md) with heritability $h^2$ be defined on a probability measure $\mu$, with $\int \beta_k \, d\mu = 0$ for every marker $k$ and $\int \varepsilon_i \, d\mu = 0$ for every individual $i$. Then for every real $N \times M$ genotype matrix $X$, every $s \in \mathbb{R}$, $c \in \mathbb{R}^N$ and every marker $j$,

$$\int \chi^2_j \, d\mu = \frac{N h^2}{M}\, \ell_j + \frac{1 - h^2}{N} \sum_{i=1}^{N} X_{ij}^2 + N s^2 \Bigl(\frac{1}{N} \sum_{i=1}^{N} X_{ij} c_i\Bigr)^2,$$

where $\chi^2_j$ is the [association statistic under stratification](chi-sq-strat.md) and $\ell_j$ the [LD score](ld-score.md), with the convention $x/0 = 0$.
