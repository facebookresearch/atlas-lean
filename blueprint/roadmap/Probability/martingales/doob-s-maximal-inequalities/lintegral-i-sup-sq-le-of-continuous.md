# Doob's $L^2$ maximal inequality in continuous time

Let $\mu$ be a probability measure, $(\mathcal{F}_t)_{t \ge 0}$ a filtration, and
$(M_t)_{t \ge 0}$ a martingale with continuous paths and $M_t \in L^2$ for every $t$. Then for
every $t \ge 0$,

$$\mathbb{E}\Big[\Big(\sup_{0 \le s \le t} |M_s|\Big)^2\Big] \le 4\, \mathbb{E}[M_t^2] .$$

## Informally uses

- [Doob's L² maximal inequality, finite horizon](doob-sq-maximal-ineq.md): applied to the
  discrete martingale $(M(tk/2^n))_{k \le 2^n}$ at each dyadic level $n$; the maxima increase with
  $n$ to the supremum over $[0, t]$ by path continuity, and monotone convergence concludes.

## Background

- [Continuous modification](../../stochastic-calculus/it-integral/ito-integral-continuous-modification.md):
  a maximal inequality of this kind is what makes the stochastic integral continuous.

## Sources

- J.-F. Le Gall, *Brownian Motion, Martingales, and Stochastic Calculus*, Graduate Texts in
  Mathematics 274, Springer, 2016, Chapter 3, section "Continuous time martingales and
  supermartingales"; the discrete-time inequality is Proposition 12.4.3 of his ENS lecture notes,
  with $p = 2$.
