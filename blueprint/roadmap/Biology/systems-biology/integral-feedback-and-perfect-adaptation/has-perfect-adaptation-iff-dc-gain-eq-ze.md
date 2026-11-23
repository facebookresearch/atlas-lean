# Perfect adaptation iff the DC gain vanishes

Let $n$ be a finite index set and let $(A, b, c, d)$ be a [linear system](../../../Analysis/control-theory/linear-system.md) $\dot x = A x + u b$, $y = c \cdot x + d u$ on $\mathbb{R}^n$, with $A$ nonsingular. The system has [perfect adaptation](has-perfect-adaptation.md)
if and only if its [DC gain](dc-gain.md) $d - c \cdot (A^{-1} b)$ is $0$.
