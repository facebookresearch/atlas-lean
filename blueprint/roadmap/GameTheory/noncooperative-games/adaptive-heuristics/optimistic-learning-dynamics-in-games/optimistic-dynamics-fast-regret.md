# Optimistic dynamics give O(T^(1/4)) individual and O(1) total regret

If every player of an $m$-player normal-form game with losses in $[0, 1]$ uses an algorithm satisfying RVU with step size $\eta$ (for example Optimistic Hedge), then for suitable $\eta$ depending on $m$ and $T$, each player's regret after $T$ rounds is $O(T^{1/4})$, with the constant polynomial in $m$ and $\log n$, and with step size $\eta = 1/(2\sqrt{m - 1})$ the sum of all players' regrets is $O(m \log n / \eta)$, independent of $T$. Consequently the time-averaged play converges to the set of coarse correlated equilibria at rate $O(1/T)$ in social welfare for smooth games.

## Proof sketch

Each player's loss vector changes by at most $(m - 1)$ times the largest change of the other players' strategies, so $\sum_t \lVert \ell_i^t - \ell_i^{t-1}\rVert_\infty^2 \le (m-1) \sum_{j \ne i} \sum_t \lVert x_j^t - x_j^{t-1}\rVert_1^2$. Summing the RVU bounds over players, the negative stability terms absorb the variation terms once $\eta$ is small enough, leaving a constant total regret. For an individual player, a second application with the trivial bound on the stability of the others gives the $T^{1/4}$ rate.

## Depends on

- [Regret bounded by variation in utilities for optimistic algorithms](rvu-property-optimistic-algorithms.md)
- [Coarse correlated equilibrium](../../no-regret-dynamics/is-coarse-correlated-eq.md)
- [Smooth game](../../no-regret-dynamics/is-smooth.md)

## Proof depends on

- [Regret bounded by variation in utilities for optimistic algorithms](rvu-property-optimistic-algorithms.md)
- [No-regret dynamics converge to coarse correlated equilibria](../../no-regret-dynamics/is-coarse-correlated-eq-empirical.md)

## Sources

- V. Syrgkanis, A. Agarwal, H. Luo, R. E. Schapire, "Fast Convergence of Regularized Learning in Games", NeurIPS 2015, arXiv:1507.00407.
