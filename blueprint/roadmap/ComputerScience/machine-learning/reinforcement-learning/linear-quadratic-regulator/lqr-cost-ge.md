# Every control sequence costs at least the Riccati value

Let $Q$ and $Q_f$ be positive semidefinite and $R$ positive definite. Then for every horizon $T$, initial state $x_0$ and control sequence $u$,

$$
x_0^\top M_T\, x_0 \le J_T(x_0, u),
$$

where $M_T$ is given by the [Riccati recursion](riccati-cost-to-go.md).

Proof: by induction on $T$. The cost splits into the stage cost at $x_0$ and the cost from $x_1 = Ax_0 + Bu_0$ over $T - 1$ steps, at least $x_1^\top M_{T-1} x_1$ by induction; their sum is the [one-step Bellman cost](bellman-cost.md), which is [at least $x_0^\top \mathcal{R}(M_{T-1}) x_0$](bellman-cost-ge.md). Positive semidefiniteness is [preserved by the update](riccati-map-pos-semidef.md).

## Sources

- B. Recht, *A tour of reinforcement learning: the view from continuous control*, Annual Review of Control, Robotics, and Autonomous Systems 2 (2019), arXiv:1806.09460, Section 4 ("the standard LQR problem admits an elegant dynamic programming solution"), for the deterministic version of problem (4.1).
