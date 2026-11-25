# Poincaré inequality with the spectral gap

Let $S$ be a finite set, $\pi$ a probability vector on $S$ ($\pi \ge 0$, $\sum_x \pi(x) = 1$), and $P$ a real $S \times S$
matrix with nonnegative entries and rows summing to $1$. Then for every $f : S \to \mathbb{R}$,

$$\lambda(P, \pi) \operatorname{Var}_\pi(f) \le \mathcal E_{\pi, P - I}(f, f),$$

where $\lambda$ is the [spectral gap](spectral-gap.md), $\operatorname{Var}_\pi$ the
[variance](weighted-variance.md) and $\mathcal E_{\pi, P - I}$ the [Dirichlet form of
$P$](form-sub-one.md). When some function has nonzero variance, $\lambda$ is the largest such
constant ([optimality](le-spectral-gap.md)).

## Sources

- P. Diaconis and L. Saloff-Coste, *Logarithmic Sobolev inequalities for finite Markov chains*, Annals of Applied Probability 6 (1996), 695–750, equation (1.4).
