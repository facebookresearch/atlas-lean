# Robust price of anarchy for no-regret dynamics

In a $(\lambda, \mu)$-smooth game with player set $I$, if after $T \ge 1$ rounds every player's
regret against every fixed strategy is at most $T \varepsilon$, then the time-averaged social cost
$A = \frac1T \sum_{t=1}^T C(s^t)$ satisfies

$$(1 - \mu)\, A \le \lambda\, C(t) + |I|\, \varepsilon$$

for every profile $t$. So when all players use no-regret algorithms the average social cost
approaches at most $\frac{\lambda}{1 - \mu}$ times the optimum, even if play never converges to an
equilibrium.

## Informally uses

- [No-regret dynamics converge to coarse correlated equilibria](is-coarse-correlated-eq-empirical.md)
  and [Extension theorem for coarse correlated equilibria](expected-social-cost-le.md).

## Sources

- T. Roughgarden, "Intrinsic robustness of the price of anarchy", J. ACM 62(5) (2015), Article 32, Theorem 3.3.
- T. Lykouris, V. Syrgkanis and É. Tardos, "Learning and efficiency in games with dynamic population", SODA 2016, arXiv:1505.00391 (the same guarantee for games whose population of learners changes over time).
