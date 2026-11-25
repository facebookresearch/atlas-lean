# Lanczos: for symmetric operators the Arnoldi matrix is tridiagonal

If $T$ is symmetric (self-adjoint) and the Krylov vectors are linearly independent, then also
$h_{ij} = 0$ for $j > i + 1$; together with the Hessenberg property, $H_k$ is tridiagonal and the
Arnoldi iteration reduces to the three-term Lanczos recurrence.

## Background

- [Conjugate gradient method](../conjugate-gradient-method/README.md): the conjugate gradient method is the Lanczos iteration applied to solving a symmetric positive definite system.

## Sources

- L. N. Trefethen and D. Bau III, Numerical Linear Algebra, SIAM (1997), Lecture 36.
- C. Lanczos, An iteration method for the solution of the eigenvalue problem of linear differential and integral operators, J. Res. Nat. Bur. Standards 45 (1950), 255–282.
