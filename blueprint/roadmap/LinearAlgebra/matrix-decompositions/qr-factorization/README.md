# QR factorization

Let $A$ be a real $m \times k$ matrix with linearly independent columns. Then $A = QR$ for an $m \times k$ matrix $Q$ with orthonormal columns, $Q^{\mathsf T} Q = I_k$, and an upper triangular $k \times k$ matrix $R$ with positive diagonal entries.

## Idea

Gram–Schmidt orthonormalization of the columns $a_1, \dots, a_k$ produces orthonormal vectors $q_1, \dots, q_k$ such that each $a_j$ is a combination of $q_1, \dots, q_j$. Collecting the coefficients $r_{ij} = \langle q_i, a_j \rangle$ gives $A = QR$ with $R$ upper triangular, and $r_{jj}$ is the length of the part of $a_j$ orthogonal to the earlier columns, positive by independence. With positive diagonal the factorization is unique. QR is the standard route to linear least squares, the basis of the QR eigenvalue algorithm and, applied to Krylov matrices, the Arnoldi iteration. Numerically one uses Householder reflections or modified Gram–Schmidt instead.

## Statements

- [Existence of the reduced QR factorization](exists-qr.md)
- [Uniqueness of the reduced QR factorization](qr-unique.md): uniqueness
- [Column of a matrix as a Euclidean vector](col-vec.md): columns as Euclidean vectors
- [The Q factor of the Gram–Schmidt QR factorization](qr-q.md): the Gram–Schmidt factor $Q$
- [The R factor of the Gram–Schmidt QR factorization](qr-r.md): the Gram–Schmidt factor $R$
- [The Gram–Schmidt Q factor has orthonormal columns](transpose-mul-qr-q.md): $Q$ has orthonormal columns
- [The Gram–Schmidt R factor is upper triangular](is-upper-triangular-qr-r.md): $R$ is upper triangular
- [The Gram–Schmidt R factor has positive diagonal](qr-r-diag-pos.md): $R$ has positive diagonal
- [Each column is the combination of the Q columns with coefficients from R](col-vec-eq-sum.md): each column is a combination of the columns of $Q$
- [The Gram–Schmidt factors reproduce the matrix](eq-qr-q-mul-qr-r.md): the factors reproduce $A$
- [Diagonal of a product of upper triangular matrices](diag-mul-of-is-upper-triangular.md): a lemma used for uniqueness
- [A Householder reflection maps a vector to a multiple of the first unit vector](householder-reflection-maps-a-vector-to-a-multiple-of-e1.md)
- [QR factorization by Householder reflections](qr-factorization-by-householder-reflections.md): the factorization used in floating point, for any $m \times n$ matrix with $m \ge n$

## Background

- [Generalized Householder matrices](../../special-matrices/generalized-householder-matrices/README.md): Householder reflections $I - 2vv^{\mathsf T}$ with $v$ a unit vector, the usual way to compute a QR factorization in floating point, are the case $\beta = 2$; the card proves that such a matrix is the reflection across $v^\perp$.

## Related topics

- [Existence and uniqueness of the least-squares solution](../linear-least-squares/exists-unique-rss-le.md): an application: least-squares problems are solved through a QR factorization.
- [Singular value decomposition of a complex matrix](../singular-value-decomposition/singular-value-decomposition-theorem/complex-singular-value-decomposition.md): another orthogonal factorization, with orthogonal factors on both sides and a diagonal middle factor.
- [LU decomposition without pivoting](../lu-decomposition/exists-lu-decomposition-of-minors-ne-zer.md): the triangular factorization by elimination, with two triangular factors and no orthogonality.
