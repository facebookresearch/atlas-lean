# Sylvester's criterion

A real symmetric $n \times n$ matrix is positive definite if and only if all its leading principal minors $\det(A_{[1..k],[1..k]})$, $1 \le k \le n$, are positive.

## Idea

Positive definiteness, $x^{\mathsf T} A x > 0$ for every nonzero $x$, is a condition on infinitely many vectors; Sylvester's criterion reduces it to $n$ determinants. Necessity holds because each leading principal submatrix is itself positive definite, so its determinant, the product of its eigenvalues, is positive. Sufficiency goes by induction: if the leading $(n-1) \times (n-1)$ block is positive definite, the whole matrix is positive definite exactly when the Schur complement of that block, a single number equal to $\det A$ divided by the previous minor, is positive. Symmetry is essential: $\begin{pmatrix} 1 & 2 \\ 0 & 1 \end{pmatrix}$ has positive leading minors but is not positive definite.

## Statements

- [Sylvester's criterion](pos-def-iff-leading-principal-minors-pos.md)
- [Leading principal submatrix](leading-principal-submatrix.md): leading principal submatrices
- [Full leading principal submatrix is the matrix itself](leading-principal-submatrix-self.md): the full one is the matrix itself
- [Positive definiteness of a block matrix via the Schur complement](from-blocks.md): positive definiteness of a bordered matrix through its Schur complement, the induction step
