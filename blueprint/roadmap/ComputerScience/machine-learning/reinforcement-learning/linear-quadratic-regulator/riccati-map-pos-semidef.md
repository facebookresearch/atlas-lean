# The Riccati update preserves positive semidefiniteness

If $Q$ and $M$ are positive semidefinite and $R$ is positive definite, then the [Riccati update](riccati-map.md) $\mathcal{R}(M)$ is positive semidefinite. It is symmetric, and $x^\top \mathcal{R}(M) x = \mathcal{B}_M(x, -Kx)$ is a sum of nonnegative quadratic forms. In particular $R + B^\top \mathcal{R}(M) B$ is positive definite, so the recursion can be continued.

## Sources

- B. Recht, *A tour of reinforcement learning: the view from continuous control*, Annual Review of Control, Robotics, and Autonomous Systems 2 (2019), arXiv:1806.09460, Section 4 (the cost-to-go matrices of the recursion are positive semidefinite).
