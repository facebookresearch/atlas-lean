# Optimistic dynamics in zero-sum games reach O(log T / T) convergence with no-regret guarantees

For two-player zero-sum matrix games with $n$ actions per player and payoffs in $[-1, 1]$, there are uncoupled no-regret dynamics such that when both players use them, the average strategies form an $O\bigl(\log n\, (\log T + (\log n)^{3/2}) / T\bigr)$-approximate Nash equilibrium after $T$ rounds, while each player's regret against an arbitrary adversary remains $O(\sqrt T \log n)$. Optimistic mirror descent with entropic regularization achieves $O(\log n / T)$ convergence of the averages when both players use it with a constant step size (for example $\eta = 1/\sqrt 8$); with adaptive step sizes and mixing in the uniform distribution it keeps $O(\sqrt{T} \log(nT))$ adversarial regret and converges at rate $O(\log(nT)/T)$.

## Proof sketch

Simulate Nesterov's excessive gap technique for the bilinear saddle point problem in a decentralized manner: each player's update uses only its own payoff vector, and the smoothing parameters are scheduled so that the duality gap decreases like $1/T$ up to logarithmic factors. Robustness against adversaries is obtained by monitoring regret and falling back to Hedge. For optimistic mirror descent, the RVU property summed over both players telescopes to a constant total regret, which bounds the duality gap of the averages by $O(\log n / T)$.

## Depends on

- [Optimistic Hedge in a repeated normal-form game](optimistic-hedge-in-games.md)
- [Nash equilibrium of a bimatrix game](../../bimatrix-games-and-the-lemke-howson-algorithm/is-bimatrix-nash.md)

## Proof depends on

- [Regret bounded by variation in utilities for optimistic algorithms](rvu-property-optimistic-algorithms.md)
- [Optimistic dynamics give O(T^(1/4)) individual and O(1) total regret](optimistic-dynamics-fast-regret.md)
- [Von Neumann's minimax theorem](../../von-neumann-s-minimax-theorem/matrix-game-minimax.md)

## Sources

- C. Daskalakis, A. Deckelbaum, A. Kim, "Near-optimal no-regret algorithms for zero-sum games", SODA 2011; Games and Economic Behavior 92 (2015), Theorem 1.
- A. Rakhlin, K. Sridharan, "Optimization, Learning, and Games with Predictable Sequences", NeurIPS 2013, arXiv:1311.1869, Proposition 6.
- V. Syrgkanis, A. Agarwal, H. Luo, R. E. Schapire, "Fast Convergence of Regularized Learning in Games", NeurIPS 2015, arXiv:1507.00407, Corollary 6.
