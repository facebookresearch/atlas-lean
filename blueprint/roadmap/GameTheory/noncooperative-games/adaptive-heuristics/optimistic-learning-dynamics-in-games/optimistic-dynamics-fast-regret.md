# Optimistic dynamics give O(T^(1/4)) individual and O(1) total regret

If every player of an $m$-player normal-form game with losses in $[0, 1]$ uses an algorithm satisfying the RVU property $\mathrm{Reg}_T \le \alpha + \beta \sum_{t} \lVert \ell^t - \ell^{t-1} \rVert_\infty^2 - \gamma \sum_{t} \lVert x^t - x^{t-1} \rVert_1^2$ with parameters depending on a step size $\eta$ (for example Optimistic Hedge, with $\alpha = (\log n)/\eta$, $\beta = \eta$, $\gamma = 1/(4\eta)$), then the following hold. If $\beta \le \gamma / (m - 1)^2$ (for Optimistic Hedge, step size $\eta \le 1/(2(m - 1))$), the sum of all players' regrets is at most $m \alpha$; for Optimistic Hedge with $\eta = 1/(2(m-1))$ this is $2 m (m - 1) \log n$, independent of $T$. With step size $\eta = (m - 1)^{-1/2} T^{-1/4}$, each player's regret after $T$ rounds is at most $(\log n + 4) \sqrt{m - 1}\, T^{1/4}$, so the empirical distribution of play is an $O(T^{-3/4})$-approximate coarse correlated equilibrium. Consequently, in a $(\lambda, \mu)$-smooth game the average social welfare is at least $\frac{\lambda}{1 + \mu} \mathrm{OPT} - O(1/T)$.

## Proof sketch

Each player's loss vector changes by at most the total movement of the other players' strategies, so $\sum_t \lVert \ell_i^t - \ell_i^{t-1}\rVert_\infty^2 \le (m-1) \sum_{j \ne i} \sum_t \lVert x_j^t - x_j^{t-1}\rVert_1^2$. Summing the RVU bounds over players, each player's movement term appears $m - 1$ times, so the variation terms total at most $\beta (m-1)^2 \sum_i \sum_t \lVert x_i^t - x_i^{t-1}\rVert_1^2$, which the negative stability terms absorb when $\beta \le \gamma / (m-1)^2$, leaving total regret at most $m \alpha$. For an individual player, the stability bound $\lVert x_j^t - x_j^{t-1} \rVert_1 \le 2\eta$ of the others gives regret at most $\alpha + \beta (m-1)^2 (2\eta)^2 T$, which is $O(T^{1/4})$ for $\eta \propto T^{-1/4}$. The welfare statement follows by summing the regret bounds in the smoothness inequality.

## Depends on

- [Optimistic Hedge in a repeated normal-form game](optimistic-hedge-in-games.md)
- [Coarse correlated equilibrium](../../no-regret-dynamics/is-coarse-correlated-eq.md)
- [Smooth game](../../no-regret-dynamics/is-smooth.md)

## Proof depends on

- [Regret bounded by variation in utilities for optimistic algorithms](rvu-property-optimistic-algorithms.md)
- [No-regret dynamics converge to coarse correlated equilibria](../../no-regret-dynamics/is-coarse-correlated-eq-empirical.md)
- [A player's loss variation is bounded by the other players' movement](loss-variation-bounded-by-opponents-movement.md)

## Sources

- V. Syrgkanis, A. Agarwal, H. Luo, R. E. Schapire, "Fast Convergence of Regularized Learning in Games", NeurIPS 2015, arXiv:1507.00407, Proposition 2, Theorem 4, Corollary 8, Theorem 11 and Corollary 12.
