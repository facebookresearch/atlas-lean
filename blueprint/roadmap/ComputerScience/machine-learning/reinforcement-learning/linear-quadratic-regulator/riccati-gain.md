# Riccati gain

For matrices $A$, $B$, $R$ and a cost-to-go matrix $M$, the Riccati gain is

$$
K = (R + B^\top M B)^{-1} B^\top M A ,
$$

where the inverse of a singular matrix is taken to be $0$. When $M$ and $R$ are symmetric and
$R + B^\top M B$ is positive definite (for instance $R$ positive definite and $M$ positive semidefinite),
$u = -Kx$ is the optimal linear control:
[it minimizes the one-step Bellman cost](bellman-cost-ge.md).

## Sources

- B. Recht, *A tour of reinforcement learning: the view from continuous control*, Annual Review of Control, Robotics, and Autonomous Systems 2 (2019), arXiv:1806.09460, Section 4.
