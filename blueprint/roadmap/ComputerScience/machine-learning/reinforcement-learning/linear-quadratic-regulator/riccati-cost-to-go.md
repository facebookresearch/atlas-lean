# Riccati recursion

Indexed by the number of remaining steps, the cost-to-go matrices of the finite-horizon problem with terminal cost $Q_f$ are

$$
M_0 = Q_f, \qquad M_{j+1} = \mathcal{R}(M_j),
$$

with $\mathcal{R}$ the [Riccati update](riccati-map.md).

## Sources

- B. Recht, *A tour of reinforcement learning: the view from continuous control*, Annual Review of Control, Robotics, and Autonomous Systems 2 (2019), arXiv:1806.09460, Section 4 (the gains $K_t$ "computed via a simple linear algebraic recursion with only knowledge of $(A, B, Q, R)$").
