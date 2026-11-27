# The linear control minimizes the one-step Bellman cost

If $M$ and $R$ are symmetric and $R + B^\top M B$ is positive definite, then for every state $x$ and control $u$,

$$
x^\top \mathcal{R}(M)\, x = \mathcal{B}_M(x, -Kx) \le \mathcal{B}_M(x, u).
$$

Proof: the square in the [completion of squares](bellman-cost-eq-add.md) is nonnegative.

## Sources

- B. Recht, *A tour of reinforcement learning: the view from continuous control*, Annual Review of Control, Robotics, and Autonomous Systems 2 (2019), arXiv:1806.09460, Section 4 ("the control action is a linear function of the state $u_t = -K_t x_t$").
