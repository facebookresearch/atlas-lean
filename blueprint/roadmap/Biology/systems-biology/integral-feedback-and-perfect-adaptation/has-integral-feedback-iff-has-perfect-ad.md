# Integral feedback is necessary

Let $n$ be a finite index set and let $(A, b, c, d)$ be a [linear system](../../../Analysis/control-theory/linear-system.md) $\dot x = A x + u b$, $y = c \cdot x + d u$ on $\mathbb{R}^n$, with $A$ nonsingular. The system has [integral feedback](has-integral-feedback.md) if
and only if it has [perfect adaptation](has-perfect-adaptation.md). When it adapts perfectly, the
functional $k$ with $k^\top = c^\top A^{-1}$ integrates the output.
