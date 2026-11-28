# Multiplicative weights diverge from interior equilibria in zero-sum games

Let $A$ be a two-player zero-sum (more generally constant-sum) matrix game with a fully mixed Nash equilibrium $(x^\star, y^\star)$. If both players run multiplicative weights (Hedge) with a constant step size, the Kullback–Leibler divergence $\mathrm{KL}(x^\star \Vert x^t) + \mathrm{KL}(y^\star \Vert y^t)$ is non-decreasing in $t$, and from every interior starting point other than an equilibrium the iterates converge to the boundary of the simplices; hence the last iterate does not converge to equilibrium. With the same fixed step size $\eta$, the time averages are guaranteed only to approach the set of $O(\eta)$-approximate Nash equilibria, by the $O(\eta)$ average regret of Hedge; the standard guarantee that time averages converge to exact equilibria uses step sizes tending to $0$. In contrast, Daskalakis and Panageas prove that when the game has a unique equilibrium (not necessarily fully mixed), optimistic multiplicative weights started from the uniform strategies with a sufficiently small constant step size (which may be changed once, between a first and a second phase) converge in the last iterate to the equilibrium.

## Proof sketch

Compute the change of the divergence in one step: it equals a first-order term that vanishes by the zero-sum structure and the equilibrium condition, plus a strictly positive second-order term from the convexity of the exponential. For the optimistic variant, the correction term cancels the second-order growth, so the divergence to the unique equilibrium decreases until the iterates are $O(\eta^{1/3})$-close to it; from there, a spectral analysis of the Jacobian of the update map shows that the equilibrium is locally asymptotically stable.

## Depends on

- [Loss of the Hedge algorithm](../../../../ComputerScience/machine-learning/online-learning-and-boosting/hedge-algorithm/alg-loss.md)
- [Nash equilibrium of a bimatrix game](../../bimatrix-games-and-the-lemke-howson-algorithm/is-bimatrix-nash.md)
- [Optimistic Hedge in a repeated normal-form game](../optimistic-learning-dynamics-in-games/optimistic-hedge-in-games.md)

## Proof depends on

- [Von Neumann's minimax theorem](../../von-neumann-s-minimax-theorem/matrix-game-minimax.md)

## Sources

- J. P. Bailey, G. Piliouras, "Multiplicative Weights Update in Zero-Sum Games", EC 2018, Theorems 3.1 and 3.3.
- C. Daskalakis, I. Panageas, "Last-Iterate Convergence: Zero-Sum Games and Constrained Min-Max Optimization", ITCS 2019, arXiv:1807.04252, Theorem 2.7.
