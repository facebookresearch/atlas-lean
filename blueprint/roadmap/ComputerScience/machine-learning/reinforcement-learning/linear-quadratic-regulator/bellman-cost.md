# One-step Bellman cost

For a state $x$, a control $u$ and a cost-to-go matrix $M$,

$$
\mathcal{B}_M(x, u) = x^\top Q x + u^\top R u + (Ax + Bu)^\top M (Ax + Bu),
$$

the stage cost plus the cost-to-go at the next state. It is the Q-function of the source's dynamic programming recursion, without the constant contributed by the noise.

## Sources

- B. Recht, *A tour of reinforcement learning: the view from continuous control*, Annual Review of Control, Robotics, and Autonomous Systems 2 (2019), arXiv:1806.09460, Section 4 (the recursion $Q_k(x, u) = x^\top Q x + u^\top R u + (Ax + Bu)^\top M_{k+1} (Ax + Bu) + c_k$).
