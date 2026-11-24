# Finite-horizon LQR cost

The cost of the control sequence $(u_t)$ from $x_0$ over $T$ steps is

$$
J_T(x_0, u) = \sum_{t=0}^{T-1} \big(x_t^\top Q x_t + u_t^\top R u_t\big) + x_T^\top Q_f x_T
$$

along the [states](lqr-state.md) of the system. This is the deterministic version of the source's problem (4.1), $\mathbb{E}\big[\tfrac12 \sum_{t=0}^{N} (x_t^\top Q x_t + u_t^\top R u_t) + \tfrac12 x_{N+1}^\top S x_{N+1}\big]$ with noise $e_t$ in the dynamics: here there is no noise, the factors $\tfrac12$ are dropped, $T = N + 1$, and $Q_f$ is the source's terminal cost $S$. The source notes that the noise does not affect how the control actions are chosen.

## Sources

- B. Recht, *A tour of reinforcement learning: the view from continuous control*, Annual Review of Control, Robotics, and Autonomous Systems 2 (2019), arXiv:1806.09460, Section 4.
