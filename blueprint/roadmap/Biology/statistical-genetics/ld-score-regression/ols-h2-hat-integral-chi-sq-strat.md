# Population consistency of the unweighted estimator

Let $\mu$ be a probability measure and $D$ an [LD-score model](model.md) under $\mu$ with $N \neq 0$
individuals, $M$ markers, heritability $h^2$, and effects $\beta_k$ and noise $\varepsilon_i$ of
mean zero. Let $X$ be a [standardized](is-standardized.md) real $N \times M$ genotype matrix with
[LD scores](ld-score.md) $\ell_j$, and let $s \in \mathbb{R}$ and $c \in \mathbb{R}^N$ be such that
the stratification term $s^2 (\sum_i X_{ij} c_i / N)^2 = a$ is the same for every marker $j$. Write
$\chi^2_j$ for the [association statistic under stratification](chi-sq-strat.md) of marker $j$.
Suppose moreover that $M \neq 0$ and that the LD scores are not all equal. Then the
[unweighted estimator](ols-h2-hat.md) applied to the expected statistics
$\mathbb{E}[\chi^2_1], \dots, \mathbb{E}[\chi^2_M]$ returns $h^2$ exactly, with or without the
confounding term $N a$.
