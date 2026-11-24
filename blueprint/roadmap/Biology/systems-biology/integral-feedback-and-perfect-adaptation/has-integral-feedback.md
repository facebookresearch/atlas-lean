# Integral feedback

Let $n$ be a finite index set and let $(A, b, c, d)$ be a [linear system](../../../Analysis/control-theory/linear-system.md) $\dot x = A x + u b$, $y = c \cdot x + d u$ on $\mathbb{R}^n$. The system has integral feedback when some linear functional $z = k \cdot x$,
$k \in \mathbb{R}^n$, integrates the output: $k \cdot (A x + u b) = c \cdot x + d u$ for every state
$x \in \mathbb{R}^n$ and every input $u \in \mathbb{R}$.
