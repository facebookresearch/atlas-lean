# Optimistic dynamics give O(T^(1/4)) individual and O(1) total regret

If every player of an $m$-player normal-form game, $m \ge 2$, with losses in $[0, 1]$ uses an algorithm satisfying the RVU property $\mathrm{Reg}_T \le \alpha + \beta \sum_{t} \lVert \ell^t - \ell^{t-1} \rVert_\infty^2 - \gamma \sum_{t} \lVert x^t - x^{t-1} \rVert_1^2$ with parameters depending on a step size $\eta$ (for example Optimistic Hedge, with $\alpha = (\log n)/\eta$, $\beta = \eta$, $\gamma = 1/(4\eta)$), then the following hold. If $\beta \le \gamma / (m - 1)^2$ (for Optimistic Hedge, step size $\eta \le 1/(2(m - 1))$), the sum of all players' regrets is at most $m \alpha$; for Optimistic Hedge with $\eta = 1/(2(m-1))$ this is $2 m (m - 1) \log n$, independent of $T$. Individual regret needs, besides the RVU inequality (here only $\alpha, \beta > 0$ and $\gamma \ge 0$ are used), the stability $\lVert x^t - x^{t-1} \rVert_1 \le \kappa$ of every player's iterates, which gives each player regret at most $\alpha + \beta \kappa^2 (m-1)^2 T$; Optimistic Hedge (optimistic follow-the-regularized-leader with the entropy regularizer and the previous loss as prediction) is stable with $\kappa = 2\eta$, so with step size $\eta = (m - 1)^{-1/2} T^{-1/4}$ each player's regret after $T$ rounds is at most $(\log n + 4) \sqrt{m - 1}\, T^{1/4}$, and the time average of the product distributions of play is an $O(T^{-3/4})$-approximate coarse correlated equilibrium. For welfare, write $u_i = 1 - \ell_i$ for the utilities, $W(s) = \sum_i u_i(s)$ and $\mathrm{OPT} = \max_s W(s)$, and call the game $(\lambda, \mu)$-smooth in the utility sense if some profile $s^\ast$ satisfies $\sum_i u_i(s_i^\ast, s_{-i}) \ge \lambda\, \mathrm{OPT} - \mu\, W(s)$ for every profile $s$; this is a welfare-maximization condition, not the cost-minimization smoothness of Roughgarden. In such a game the average expected welfare of play is at least $\frac{\lambda}{1 + \mu} \mathrm{OPT} - \frac{1}{(1 + \mu) T} \sum_i \mathrm{Reg}_{i,T}$, so in the constant-total-regret regime $\beta \le \gamma/(m-1)^2$ it is at least $\frac{\lambda}{1 + \mu} \mathrm{OPT} - \frac{m \alpha}{(1 + \mu) T}$.

## Proof sketch

Each player's loss vector changes by at most the total movement of the other players' strategies, so $\sum_t \lVert \ell_i^t - \ell_i^{t-1}\rVert_\infty^2 \le (m-1) \sum_{j \ne i} \sum_t \lVert x_j^t - x_j^{t-1}\rVert_1^2$. Summing the RVU bounds over players, each player's movement term appears $m - 1$ times, so the variation terms total at most $\beta (m-1)^2 \sum_i \sum_t \lVert x_i^t - x_i^{t-1}\rVert_1^2$, which the negative stability terms absorb when $\beta \le \gamma / (m-1)^2$, leaving total regret at most $m \alpha$. For an individual player, the stability bound $\lVert x_j^t - x_j^{t-1} \rVert_1 \le \kappa$ of the others bounds each squared loss variation by $(m-1)^2\kappa^2$, so the RVU bound with its negative term dropped gives regret at most $\alpha + \beta (m-1)^2 \kappa^2 T$; with $\kappa = 2\eta$ this is $O(T^{1/4})$ for $\eta \propto T^{-1/4}$. The welfare statement follows by applying the smoothness inequality to the time-averaged play and adding the players' regret bounds.

## Depends on

- [Optimistic Hedge in a repeated normal-form game](optimistic-hedge-in-games.md)
- [Coarse correlated equilibrium](../../no-regret-dynamics/is-coarse-correlated-eq.md)

## Proof depends on

- [Regret bounded by variation in utilities for optimistic algorithms](rvu-property-optimistic-algorithms.md)
- [No-regret dynamics converge to coarse correlated equilibria](../../no-regret-dynamics/is-coarse-correlated-eq-empirical.md)
- [A player's loss variation is bounded by the other players' movement](loss-variation-bounded-by-opponents-movement.md)

## Sources

- V. Syrgkanis, A. Agarwal, H. Luo, R. E. Schapire, "Fast Convergence of Regularized Learning in Games", NeurIPS 2015, arXiv:1507.00407, Definition 1, Proposition 2, Theorem 4, Proposition 7, Corollary 8, Theorem 11 and Corollary 12.
