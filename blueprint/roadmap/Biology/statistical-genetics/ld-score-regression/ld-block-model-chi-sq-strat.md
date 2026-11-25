# LD-block model for the association statistics from fourth moments

Let $\mu$ be a probability measure and $D$ an [LD-score model](model.md) under $\mu$ with $N \neq 0$
individuals, $M$ markers, heritability $h^2$, and effects $\beta_k$ and noise $\varepsilon_i$ of
mean zero. Let $X$ be a [standardized](is-standardized.md) real $N \times M$ genotype matrix with
[LD scores](ld-score.md) $\ell_j$, and let $s \in \mathbb{R}$ and $c \in \mathbb{R}^N$ be such that
the stratification term $s^2 (\sum_i X_{ij} c_i / N)^2 = a$ is the same for every marker $j$. Write
$\chi^2_j$ for the [association statistic under stratification](chi-sq-strat.md) of marker $j$.
Suppose that the [normalized scores under stratification](beta-hat-strat.md) $\hat\beta_j$ satisfy a
[score-level LD-block model](score-block-model.md) with block size $K$, and let $\kappa_4 \geq 0$,
$L$, $\lambda$ and $A$ be real numbers with
$\mathbb{E}[(\chi^2_j)^2] \leq \kappa_4 (\mathbb{E}[\chi^2_j])^2$ for every marker $j$ (a kurtosis
bound), $\ell_j \leq L$ for every $j$, $N \leq \lambda M$ and $N a \leq A$. Then the statistics
$\chi^2_1, \dots, \chi^2_M$ satisfy an [LD-block model](ldblock-model.md) with block size $K$ and
variance bound $\kappa_4 (1 + \lambda L + A)^2$.
