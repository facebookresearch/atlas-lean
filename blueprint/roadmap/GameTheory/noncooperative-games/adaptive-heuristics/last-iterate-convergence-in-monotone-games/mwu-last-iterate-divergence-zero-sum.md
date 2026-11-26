# Multiplicative weights diverge from interior equilibria in zero-sum games

Let $A$ be a two-player zero-sum matrix game with a unique fully mixed Nash equilibrium $(x^\star, y^\star)$. If both players run multiplicative weights (Hedge) with any constant step size from any interior starting point other than the equilibrium, the Kullback–Leibler divergence $\mathrm{KL}(x^\star \Vert x^t) + \mathrm{KL}(y^\star \Vert y^t)$ is strictly increasing in $t$, and the iterates approach the boundary of the simplices; hence the last iterate does not converge to equilibrium even though time-averages do. In contrast optimistic multiplicative weights converge in the last iterate to the equilibrium.

## Proof sketch

Compute the change of the divergence in one step: it equals a first-order term that vanishes by the zero-sum structure and the equilibrium condition, plus a strictly positive second-order term from the convexity of the exponential. For the optimistic variant, the correction term cancels the second-order growth and an energy argument shows decrease of a modified divergence.

## Depends on

- [Von Neumann's minimax theorem](../../von-neumann-s-minimax-theorem/matrix-game-minimax.md)
- [Loss of the Hedge algorithm](../../../../ComputerScience/machine-learning/online-learning-and-boosting/hedge-algorithm/alg-loss.md)

## Proof depends on

- [Von Neumann's minimax theorem](../../von-neumann-s-minimax-theorem/matrix-game-minimax.md)

## Sources

- J. P. Bailey, G. Piliouras, "Multiplicative Weights Update in Zero-Sum Games", EC 2018.
- C. Daskalakis, I. Panageas, "Last-Iterate Convergence: Zero-Sum Games and Constrained Min-Max Optimization", ITCS 2019, arXiv:1807.04252.
