# Simultaneous diagonalization by congruence

Let $S$ and $P$ be real square matrices indexed by a finite set, with $S$ symmetric and $P$ positive definite. Then there is an invertible real matrix $C$ such that $C^{\mathsf T} S C$ is diagonal and $C^{\mathsf T} P C$ is the identity matrix.

## Idea

A positive definite matrix defines an inner product, and in an orthonormal basis for that inner product it becomes the identity. The second form $S$ is then a symmetric matrix in an inner-product space, and the spectral theorem diagonalizes it by an orthogonal change of basis, which keeps the identity unchanged. Congruence, $X \mapsto C^{\mathsf T} X C$, is the change of basis for bilinear forms, so the result says that two quadratic forms, one of them positive definite, have a common diagonalizing basis. The diagonal entries are the generalized eigenvalues of the pencil $S - \lambda P$; the theorem is used in mechanics for small oscillations and in statistics for discriminant analysis.

## Statements

- [Simultaneous diagonalization by congruence](simultaneous-diagonalization-pos-def.md)
- [Positive-definite matrices are congruent to the identity](exists-is-unit-transpose-mul-mul-eq-one.md): first step: a positive definite matrix is congruent to the identity
