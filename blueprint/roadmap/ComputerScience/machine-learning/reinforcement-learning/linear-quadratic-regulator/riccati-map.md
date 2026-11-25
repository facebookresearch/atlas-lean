# Riccati update

The Riccati update of a cost-to-go matrix $M$ is

$$
\mathcal{R}(M) = Q + A^\top M A - (A^\top M B)(R + B^\top M B)^{-1}(B^\top M A),
$$

where the inverse of a singular matrix is taken to be $0$. When $M$ and $R$ are symmetric and $R + B^\top M B$ is positive definite, it is the matrix of the optimal cost-to-go one step earlier: the [linear control minimizes the one-step Bellman cost](bellman-cost-ge.md), and the [Bellman cost of the linear control](bellman-cost-neg-gain.md) is the quadratic form of $\mathcal{R}(M)$. Its fixed points $M = \mathcal{R}(M)$ are the solutions of the discrete algebraic Riccati equation (4.2) of the source, which describes the infinite-horizon problem; that limit is not treated here.

## Sources

- B. Recht, *A tour of reinforcement learning: the view from continuous control*, Annual Review of Control, Robotics, and Autonomous Systems 2 (2019), arXiv:1806.09460, Section 4, equation (4.2).
