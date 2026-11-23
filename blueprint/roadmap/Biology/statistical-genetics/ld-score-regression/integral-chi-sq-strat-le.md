# Bounded LD bounds the expected statistic

Let $\mu$ be a probability measure and $D$ an [LD-score model](model.md) under $\mu$ with $N \neq 0$
individuals, $M$ markers, heritability $h^2$, and effects $\beta_k$ and noise $\varepsilon_i$ of
mean zero. Let $X$ be a [standardized](is-standardized.md) real $N \times M$ genotype matrix with
[LD scores](ld-score.md) $\ell_j$, and let $s \in \mathbb{R}$ and $c \in \mathbb{R}^N$ be such that
the stratification term $s^2 (\sum_i X_{ij} c_i / N)^2 = a$ is the same for every marker $j$. Write
$\chi^2_j$ for the [association statistic under stratification](chi-sq-strat.md) of marker $j$. Let
$L$, $\lambda$ and $A$ be real numbers with $\ell_j \leq L$ for every marker $j$, $N \leq \lambda M$
and $N a \leq A$. Then $0 \leq \mathbb{E}[\chi^2_j] \leq 1 + \lambda L + A$ for every marker $j$.
