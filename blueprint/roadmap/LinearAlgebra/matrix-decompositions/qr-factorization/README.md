# QR factorization

Every real matrix with linearly independent columns factors as $A = QR$ with $Q$ having orthonormal columns and $R$ upper triangular with positive diagonal, and the factorization is unique (Trefethen and Bau, Lecture 7). Here $Q$ and $R$ are produced by Gram–Schmidt orthonormalization of the columns; numerically one uses modified Gram–Schmidt or Householder triangularization, which in exact arithmetic give the same factors up to the signs of the columns of $Q$ and the rows of $R$. QR is the standard route to [linear least squares](../linear-least-squares/README.md), the first step of the QR eigenvalue algorithm, and, applied to Krylov matrices, the Arnoldi iteration behind GMRES.

- [Column of a matrix as a Euclidean vector](col-vec.md)
- [The Q factor of the Gram–Schmidt QR factorization](qr-q.md)
- [The R factor of the Gram–Schmidt QR factorization](qr-r.md)
- [The Gram–Schmidt Q factor has orthonormal columns](transpose-mul-qr-q.md)
- [The Gram–Schmidt R factor is upper triangular](is-upper-triangular-qr-r.md)
- [The Gram–Schmidt R factor has positive diagonal](qr-r-diag-pos.md)
- [Each column is the combination of the Q columns with coefficients from R](col-vec-eq-sum.md)
- [The Gram–Schmidt factors reproduce the matrix](eq-qr-q-mul-qr-r.md)
- [Existence of the reduced QR factorization](exists-qr.md)
- [Diagonal of a product of upper triangular matrices](diag-mul-of-is-upper-triangular.md)
- [Uniqueness of the reduced QR factorization](qr-unique.md)

## Related topics

- [Linear least squares](../linear-least-squares/README.md)
- [Singular value decomposition](../singular-value-decomposition/README.md)
- [LU decomposition](../lu-decomposition/README.md)
- [Generalized Householder matrices](../../special-matrices/generalized-householder-matrices/README.md)
