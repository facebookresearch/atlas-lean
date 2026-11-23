# Finite termination of GMRES

If $A$ is an invertible real $n \times n$ matrix, every $n$-th GMRES iterate solves $Ax = b$
exactly (in exact arithmetic).

Proof: take $p = \chi_A / \chi_A(0)$, the characteristic polynomial normalized at $0$
($\chi_A(0) = \pm \det A \ne 0$); by Cayley–Hamilton $p(A) = 0$.

## Sources

- L. N. Trefethen and D. Bau III, Numerical Linear Algebra, SIAM (1997), Lecture 35.
