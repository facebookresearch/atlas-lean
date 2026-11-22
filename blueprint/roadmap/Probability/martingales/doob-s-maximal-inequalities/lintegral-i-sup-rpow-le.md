# Doob's $L^p$ maximal inequality in continuous time

Let $\mu$ be a probability measure, $(\mathcal{F}_t)_{t \ge 0}$ a filtration, and
$(X_t)_{t \ge 0}$ a nonnegative submartingale with continuous paths, and let $p > 1$. Then for
every $t \ge 0$,

$$\mathbb{E}\Big[\Big(\sup_{0 \le s \le t} X_s\Big)^p\Big] \le \Big(\frac{p}{p-1}\Big)^p\, \mathbb{E}[X_t^p] .$$

The expectations are integrals of $[0, \infty]$-valued functions, so the statement needs no
integrability assumption on $X_t^p$.

The case $p = 2$ for martingales is
[Doob's $L^2$ maximal inequality in continuous time](lintegral-i-sup-sq-le-of-continuous.md).

The proof applies the discrete-time $L^p$ inequality along the dyadic times of $[0, t]$;
continuity identifies the supremum over the dyadic times with the supremum over $[0, t]$, and
monotone convergence concludes.

## Background

- [Doob's L² maximal inequality, finite horizon](doob-sq-maximal-ineq.md): the discrete-time
  inequality for $p = 2$.

## Sources

- J.-F. Le Gall, *Brownian Motion, Martingales, and Stochastic Calculus*, Graduate Texts in
  Mathematics 274, Springer, 2016, Chapter 3, section "Continuous time martingales and
  supermartingales"; the discrete-time inequality is Proposition 12.4.3 of his ENS lecture notes.
