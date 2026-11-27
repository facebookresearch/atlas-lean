# Extension theorem for coarse correlated equilibria

In a $(\lambda, \mu)$-smooth game with player set $I$, every $\varepsilon$-coarse correlated
equilibrium (additive error $\varepsilon$) $\sigma$ satisfies

$$(1 - \mu)\, \mathbb E_{s \sim \sigma}[C(s)] \le \lambda\, C(t) + |I|\, \varepsilon$$

for every profile $t$. For $\mu < 1$ and $\varepsilon = 0$ this is
$\mathbb E_\sigma[C] \le \frac{\lambda}{1 - \mu}\, C(t)$: price-of-anarchy bounds proved by smoothness
hold for coarse correlated equilibria, not only for Nash equilibria.

## Background

- [Smooth game](is-smooth.md), applied to each profile in the support of $\sigma$ with deviations
  $t_i$.

## Sources

- T. Roughgarden, "Intrinsic robustness of the price of anarchy", J. ACM 62(5) (2015), Article 32, Theorem 3.2 (stated for $\varepsilon = 0$; the additive $\varepsilon$ term follows the
  same proof with the approximate equilibrium of Lecture 17, Proposition 3.1).
- T. Roughgarden, CS364A *Algorithmic Game Theory*, Lecture #17 "No-regret dynamics", Stanford University, 2013,
  Proposition 3.1.
