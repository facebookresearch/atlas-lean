# Optimistic Hedge achieves polylogarithmic individual regret in general-sum games

If all $m$ players of a finite general-sum normal-form game with $n$ actions per player and losses in $[0, 1]$ run Optimistic Hedge with a suitable constant step size $\eta = \Theta\bigl(1/(m \log^4 T)\bigr)$, then every player's regret after $T$ rounds is

$$
O\bigl(m \log n \cdot \log^4 T\bigr).
$$

Consequently the empirical distribution of play is an $O\bigl(m \log n \log^4 T / T\bigr)$-approximate coarse correlated equilibrium.

## Proof sketch

A refined adversarial regret bound for Optimistic Hedge gives $\mathrm{Reg}_{i,T} \le \frac{\log n}{\eta} + \sum_t \bigl(\tfrac{\eta}{2} + C\eta^2\bigr) \mathrm{Var}_{x_i^t}(\ell_i^t - \ell_i^{t-1}) - \sum_t \tfrac{(1 - C\eta)\eta}{2} \mathrm{Var}_{x_i^t}(\ell_i^{t-1})$, with variances taken under the player's own mixed strategy. When all players run Optimistic Hedge, the order-$h$ finite differences of the loss sequences are $O(m\eta)^h h^{O(h)}$ for $h \le \log T$, and a downward induction on $h$ using the discrete Fourier transform and Parseval's identity shows $\sum_t \mathrm{Var}(\ell_i^t - \ell_i^{t-1}) \le \tfrac12 \sum_t \mathrm{Var}(\ell_i^{t-1}) + O(\log^5 T)$. The negative term then absorbs the variation, leaving $\log n / \eta + O(\eta \log^5 T)$.

## Depends on

- [Optimistic Hedge in a repeated normal-form game](optimistic-hedge-in-games.md)
- [Coarse correlated equilibrium](../../no-regret-dynamics/is-coarse-correlated-eq.md)

## Proof depends on

- [Regret bounded by variation in utilities for optimistic algorithms](rvu-property-optimistic-algorithms.md)
- [Higher-order smoothness of Optimistic Hedge iterates](higher-order-smoothness-optimistic-hedge.md)
- [No-regret dynamics converge to coarse correlated equilibria](../../no-regret-dynamics/is-coarse-correlated-eq-empirical.md)

## Sources

- C. Daskalakis, M. Fishelson, N. Golowich, "Near-Optimal No-Regret Learning in General Games", NeurIPS 2021, arXiv:2108.06924, Theorem 3.1 and Lemmas 4.1 and 4.2.
