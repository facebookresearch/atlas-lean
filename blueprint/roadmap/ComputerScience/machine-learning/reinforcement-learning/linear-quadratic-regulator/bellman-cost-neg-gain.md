# The Bellman cost of the linear control

Under the hypotheses of the [completion of squares](bellman-cost-eq-add.md),

$$
\mathcal{B}_M(x, -Kx) = x^\top \mathcal{R}(M)\, x,
$$

where $\mathcal{R}(M)$ is the [Riccati update](riccati-map.md): the optimal one-step cost is again a quadratic form.

## Sources

- B. Recht, *A tour of reinforcement learning: the view from continuous control*, Annual Review of Control, Robotics, and Autonomous Systems 2 (2019), arXiv:1806.09460, Section 4 (the recursion for the matrices $M_k$, whose limit solves (4.2)).
