# Vanishing estimator variance along a sequence of block designs

Let $\nu$ be a probability measure on $\mathbb{R}$ satisfying the
[bounded unit law](is-bounded-unit-law.md) condition with bound $C$, and $h^2 \in [0, 1]$. Along a
filter on an index set, let $D_n$ be [block designs](block-design.md) with $N_n$ individuals, $M_n$
markers, block size $K$ and cohort size $G$, the same for every $n$, and let $\ell_n$ be the
[LD scores](ld-score.md) of the genotype matrix of $D_n$. Suppose that there are real numbers
$\kappa > 0$, $\lambda$ and $c > 0$ with $\kappa M_n \leq N_n \leq \lambda M_n$ and
$S_{\ell_n \ell_n} \geq c M_n$ for all $n$, where $S_{\ell\ell} = \sum_j (\ell_j - \bar\ell)^2$ is
the spread of the LD scores, and that $M_n \to \infty$. Then the variance of the
[unweighted estimator](ols-h2-hat.md) $\hat h^2_n$ computed from $\ell_n$ and the statistics
$\chi^2_{n,j}$ of the [model on the product space](model-2.md) with $N_n$ individuals and $M_n$
markers, without stratification, tends to $0$.
