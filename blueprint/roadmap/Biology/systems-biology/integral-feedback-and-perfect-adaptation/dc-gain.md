# Steady-state (DC) gain of a linear system

Let $n$ be a finite index set and let $(A, b, c, d)$ be a [linear system](linear-system.md) $\dot x = A x + u b$, $y = c \cdot x + d u$ on $\mathbb{R}^n$. Its steady-state (DC) gain is $d - c \cdot (A^{-1} b)$, where $A^{-1}$ is read as the
zero matrix when $A$ is singular. For nonsingular $A$, the [output at the equilibrium](output-equilibrium.md)
for a constant input $u$ is the DC gain times $u$.
