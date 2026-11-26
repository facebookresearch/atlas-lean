# Optimistic Hedge achieves polylogarithmic individual regret in general-sum games

If all $m$ players of a finite general-sum normal-form game with $n$ actions per player and losses in $[0, 1]$ run Optimistic Hedge with a suitable constant step size $\eta = \Theta\bigl(1/(m \log^4 T)\bigr)$, then every player's regret after $T$ rounds is

$$
O\bigl(m \log n \cdot \log^4 T\bigr).
$$

Consequently the empirical distribution of play is an $O\bigl(m \log n \log^4 T / T\bigr)$-approximate coarse correlated equilibrium.

## Proof sketch

Bound the variation of each player's loss sequence through the higher-order smoothness of Optimistic Hedge: the iterates $x^t$, viewed as a function of $t$, have finite differences of order $h$ decaying geometrically like $(O(\eta h))^{h}$ in an appropriate norm. A discrete Fourier-type argument (bounding a sequence's second-moment variation by its higher-order differences) then shows that $\sum_t \lVert \ell_i^t - \ell_i^{t-1}\rVert^2$ is at most $O(\log^4 T)$ times a small multiple of $\sum_t \lVert x_i^t - x_i^{t-1}\rVert^2$ plus a polylogarithmic term, so the RVU negative term absorbs it for each player individually.

## Depends on

- [Optimistic Hedge in a repeated normal-form game](optimistic-hedge-in-games.md)
- [Coarse correlated equilibrium](../../no-regret-dynamics/is-coarse-correlated-eq.md)

## Proof depends on

- [Regret bounded by variation in utilities for optimistic algorithms](rvu-property-optimistic-algorithms.md)
- [Higher-order smoothness of Optimistic Hedge iterates](higher-order-smoothness-optimistic-hedge.md)
- [No-regret dynamics converge to coarse correlated equilibria](../../no-regret-dynamics/is-coarse-correlated-eq-empirical.md)

## Sources

- C. Daskalakis, M. Fishelson, N. Golowich, "Near-Optimal No-Regret Learning in General Games", NeurIPS 2021, arXiv:2108.06924.
