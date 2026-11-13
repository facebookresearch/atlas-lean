# Spectral theorem for normal matrices

Let $M$ be a complex square matrix whose rows and
columns are indexed by a finite set $n$, and write $M^*$ for its conjugate transpose. If $M$ is
normal, that is, $M^* M = M M^*$, then there exist a unitary matrix $P$ indexed by $n$ (so
$P^* P = P P^* = I$) and a family of complex numbers $(d_i)_{i \in n}$ such that $P^* M P$ is
the diagonal matrix with diagonal entries $d_i$.

## Sources

- AlgebraNotes, Section: The Spectral Theorem, Subsection: The Spectral Theorem, Theorem (Spectral Theorem) (normal-matrix case; the Hermitian cases are Mathlib's `Matrix.IsHermitian.spectral_theorem`).
