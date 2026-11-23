# Schur decomposition

Let $A$ be a complex square matrix indexed by a finite linearly ordered set. Then $A = UTU^*$ for some unitary matrix $U$ and some upper triangular matrix $T$ ($T_{ij} = 0$ whenever $j < i$).

## Idea

Over the complex numbers every matrix has an eigenvector. Normalize one, extend it to an orthonormal basis, and the first column of the matrix in that basis is zero below the diagonal; induction on the remaining block finishes the proof. The diagonal of $T$ lists the eigenvalues with multiplicity. Because $U$ is unitary, the change of basis is perfectly conditioned, which makes the Schur form, rather than the Jordan form, the target of numerical eigenvalue algorithms such as the QR algorithm. For a normal matrix $T$ is diagonal, which is the spectral theorem.

## Statements

- [Schur decomposition of a complex square matrix](exists-unitary-group-is-upper-triangular.md)
