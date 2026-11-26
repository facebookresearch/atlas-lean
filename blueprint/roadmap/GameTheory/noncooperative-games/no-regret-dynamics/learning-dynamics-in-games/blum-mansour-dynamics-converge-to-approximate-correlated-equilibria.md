# Blum–Mansour dynamics converge to approximate correlated equilibria

Let $G$ be a finite cost game with all costs in $[-1, 1]$, $m_i = |S_i| \ge 2$, and horizon $T \ge \max_i m_i \ln m_i$. If player $i$'s swap regret over the coupled play is at most $R_i$, then the time-averaged product distribution $\frac1T \sum_t \prod_i p^t_i$ is an $(R_i/T)$-approximate correlated equilibrium for player $i$. For Blum–Mansour dynamics one may take $R_i / T \le 2\sqrt{m_i \ln m_i / T}$, so the time average is a $\max_i 2\sqrt{m_i \ln m_i / T}$-approximate correlated equilibrium.

## Proof sketch

The stationary-distribution step makes the player's realized cost equal to the sum of the copies' charged costs, so swap regret is at most the sum of the copies' external regrets. Each copy runs Hedge and has regret $O(\sqrt{(T/m_i)\ln m_i})$ in its own scaled losses; summing gives the bound. Swap regret bounded by $R_i$ is exactly the approximate correlated-equilibrium condition for the time average.

## Depends on

- [Coupled Blum–Mansour swap-regret dynamics](coupled-blum-mansour-swap-regret-dynamics.md)
- [Correlated equilibrium](../../correlated-equilibria/is-correlated-eq.md)

## Proof depends on

- [Blum–Mansour decomposition](../../../not-yet-classified/part-02/regret-blum-mansour/swap-regret-le-sum-external-regret-scale.md)
- [Each player in Hedge dynamics has vanishing regret](each-player-in-hedge-dynamics-has-vanishing-regret.md)

## Sources

- Avrim Blum and Yishay Mansour, "From External to Internal Regret", Journal of Machine Learning Research, 2007.
- Tim Roughgarden, "CS364A: Algorithmic Game Theory, Lecture Notes", Stanford University, Fall 2013, 2013.
