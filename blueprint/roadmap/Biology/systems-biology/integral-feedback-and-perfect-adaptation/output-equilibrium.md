# Output at equilibrium equals DC gain times input

Let $n$ be a finite index set and let $(A, b, c, d)$ be a [linear system](linear-system.md) $\dot x = A x + u b$, $y = c \cdot x + d u$ on $\mathbb{R}^n$. For every $u \in \mathbb{R}$, the output at the state $x = -u A^{-1} b$ and input $u$
equals the [DC gain](dc-gain.md) times $u$, with $A^{-1}$ read as the zero matrix when $A$ is singular.
For nonsingular $A$ this state is the [unique equilibrium](field-eq-zero-iff.md) for the input $u$.
