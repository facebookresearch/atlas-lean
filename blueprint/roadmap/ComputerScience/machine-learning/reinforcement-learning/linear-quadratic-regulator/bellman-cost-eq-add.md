# Completion of squares in the control

Let $M$ and $R$ be symmetric and let $S = R + B^\top M B$ be invertible, with $K$ the [Riccati gain](riccati-gain.md). Then for every state $x$ and control $u$,

$$
\mathcal{B}_M(x, u) = \mathcal{B}_M(x, -Kx) + (u + Kx)^\top S\, (u + Kx).
$$

Proof: $\mathcal{B}_M(x, u) = x^\top (Q + A^\top M A) x + u^\top S u + 2 u^\top g$ with $g = B^\top M A x = S K x$; expand the square.

## Sources

- B. Recht, *A tour of reinforcement learning: the view from continuous control*, Annual Review of Control, Robotics, and Autonomous Systems 2 (2019), arXiv:1806.09460, Section 4 (the dynamic programming derivation of the linear optimal control).
