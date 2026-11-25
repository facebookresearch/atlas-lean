# Triangularization of an endomorphism with split characteristic polynomial

Let $V$ be a
finite-dimensional vector space over a field $K$, let $f$ be an endomorphism of $V$ whose
characteristic polynomial splits over $K$, and let $\iota$ be a finite linearly ordered set with
exactly $\dim_K V$ elements. Then there is a basis $(b_i)_{i \in \iota}$ of $V$ in which the matrix
of $f$ is upper triangular: its $(i, j)$ entry is $0$ whenever $j < i$.

Proof: induction on dimension. An eigenvector spans an invariant line, the induced map on the
quotient has split minimal polynomial (it divides that of $f$), and a triangularizing basis of the
quotient lifts, together with the eigenvector, to one of $V$. This is the eigenvector-deflation
induction of the proof of Schur's theorem in R. A. Horn and C. R. Johnson, Matrix Analysis, 2nd
ed., Cambridge University Press (2013), Theorem 2.3.1, without unitarity.

## Sources

- S. Axler, Linear Algebra Done Right, 4th ed., Springer (2024), Theorem 5.41.
