# Completing the square for one LQR stage

Let $P, Q$ be positive semidefinite and $R$ positive definite, let $K = (R + B^\top P B)^{-1} B^\top P A$ and let $P'$ be the Riccati step $Q + A^\top P A - A^\top P B (R + B^\top P B)^{-1} B^\top P A$. Then every state $x$ and input $u$ satisfy

$$x^\top Q x + u^\top R u + (Ax + Bu)^\top P (Ax + Bu) = x^\top P' x + (u + Kx)^\top (R + B^\top P B)(u + Kx).$$

The same identity follows, under weaker hypotheses (symmetric $P$ and $R$ and invertible $R + B^\top P B$), from the [expansion of the one-stage Bellman cost](../../../../ComputerScience/machine-learning/reinforcement-learning/linear-quadratic-regulator/bellman-cost-eq-add.md) and [its value at the negative gain](../../../../ComputerScience/machine-learning/reinforcement-learning/linear-quadratic-regulator/bellman-cost-neg-gain.md).
