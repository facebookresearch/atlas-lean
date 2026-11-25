# Vanishing estimator variance for association statistics in LD blocks

Let $\mu$ be a finite measure and, along a filter on an index set, let $D_n$ be
[LD-score models](model.md) under $\mu$ with $N_n$ individuals and $M_n$ markers, $X_n$ real
$N_n \times M_n$ matrices with [LD scores](ld-score.md) $\ell_{n,j}$, and $s_n \in \mathbb{R}$,
$c_n \in \mathbb{R}^{N_n}$. Suppose that the
[association statistics under stratification](chi-sq-strat.md) $\chi^2_{n,j}$ of every design
satisfy an [LD-block model](ldblock-model.md) with block size $K$ and variance bound $V$, the same
for every $n$, that $M_n \to \infty$, and that $N_n \geq \kappa M_n$ and
$S_{\ell_n \ell_n} \geq c_0 M_n$ for all $n$, for some $\kappa > 0$ and $c_0 > 0$. Then the
variance, a value in $[0, \infty]$, of the [unweighted estimator](ols-h2-hat.md) $\hat h^2_n$ tends
to $0$. This is the vanishing-variance hypothesis of
[the consistency theorem](tendsto-in-measure-ols-h2-hat.md).
