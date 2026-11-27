# Variance bound for the estimator along a block design

For a [block design](block-design.md) with $N$ individuals, $M$ markers, block size $K$, cohort size
$G$ and genotype matrix $X$, a probability measure $\nu$ on $\mathbb{R}$ satisfying the
[bounded unit law](is-bounded-unit-law.md) condition with bound $C$, $h^2 \in [0, 1]$ and
$\lambda \geq 0$ with $N \leq \lambda M$, the [unweighted estimator](ols-h2-hat.md) $\hat h^2$
computed from the [LD scores](ld-score.md) $\ell$ of $X$ and the statistics
$\chi^2_1, \dots, \chi^2_M$ of the [model on the product space](model-2.md), without stratification,
satisfies

$$\operatorname{Var}(\hat h^2) \leq \Bigl(\frac{M}{N}\Bigr)^2 \frac{K (B/2)^2}{S_{\ell\ell}},$$

where $B = G \cdot 2 C^2 (K^2 \lambda + 1)$ is the [bound constant](chi-sq-bound.md),
$S_{\ell\ell} = \sum_j (\ell_j - \bar\ell)^2$ is the spread of the LD scores and $x/0 = 0$.
