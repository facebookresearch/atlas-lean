# Integral-feedback functional is the time integral of the output

Let $n$ be a finite index set and let $(A, b, c, d)$ be a [linear system](linear-system.md) $\dot x = A x + u b$, $y = c \cdot x + d u$ on $\mathbb{R}^n$, and let $k \in \mathbb{R}^n$ satisfy $k \cdot (A x + u b) = c \cdot x + d u$ for all
$x \in \mathbb{R}^n$ and $u \in \mathbb{R}$. If $x \colon \mathbb{R} \to \mathbb{R}^n$ and
$u \colon \mathbb{R} \to \mathbb{R}$ are such that $x$ has derivative $A x(t) + u(t) b$ at $t$, then
$s \mapsto k \cdot x(s)$ has derivative $y(t) = c \cdot x(t) + d u(t)$ at $t$: the functional
$k \cdot x$ is the time integral of the output.
