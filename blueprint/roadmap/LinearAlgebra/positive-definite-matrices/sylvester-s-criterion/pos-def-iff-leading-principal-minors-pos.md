# Sylvester's criterion

Let $A$ be a real symmetric $n \times n$ matrix. Then $A$ is positive definite if and only if all its
leading principal minors $\det\bigl(A_{[1..k],[1..k]}\bigr)$, $0 \le k \le n$, are positive (the
empty minor, $k = 0$, equals $1$).

Symmetry is essential: $\begin{pmatrix} 1 & 2 \\ 0 & 1 \end{pmatrix}$ has leading principal minors
$1$ and $1$ but is not symmetric, hence not positive definite.
