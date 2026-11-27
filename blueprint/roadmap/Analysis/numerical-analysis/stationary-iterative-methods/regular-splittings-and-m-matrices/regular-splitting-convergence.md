# Convergence of regular splittings

Let $(M, N)$ be a [regular splitting](regular-splitting.md) of a real $n \times n$ matrix $A$. Then

$$\rho(M^{-1}N) < 1 \iff A \text{ is nonsingular and } A^{-1} \text{ has nonnegative entries.}$$

So for a [nonsingular M-matrix](../../../../LinearAlgebra/special-matrices/m-matrices-and-hurwitz-stability/nonsingular-m-matrices/is-nonsingular-mmatrix.md), whose inverse is nonnegative, every regular splitting, for instance the Jacobi splitting, gives a convergent iteration. The proof writes $A = M(I - G)$ with $G = M^{-1}N \ge 0$ and, for the converse, shows that $A^{-1}N = (I - G)^{-1} G$ is nonnegative, so that an eigenvector of $G$ for $\rho(G)$ gives $\rho(G)/(1 - \rho(G)) \ge 0$.

## Depends on

- [Regular splitting](regular-splitting.md)
- [Nonsingular M-matrix](../../../../LinearAlgebra/special-matrices/m-matrices-and-hurwitz-stability/nonsingular-m-matrices/is-nonsingular-mmatrix.md)
- [A Z-matrix is a nonsingular M-matrix if and only if its inverse is nonnegative](z-matrix-is-a-nonsingular-m-matrix-iff-its-inverse-is-nonnegative.md)
- [Jacobi and Gauss–Seidel iteration matrices](../jacobi-and-gauss-seidel-iteration-matrices.md)

## Proof depends on

- [A nonnegative inverse of I − B forces ρ(B) < 1](nonnegative-inverse-forces-spectral-radius-below-one.md)
- [Perron eigenvector of a nonnegative matrix](perron-eigenvector-of-a-nonnegative-matrix.md)

## Sources

- Y. Saad, *Iterative Methods for Sparse Linear Systems*, 2nd edition, SIAM, 2003, Section 4.2.2, Theorem 4.4 (Varga) and its proof through (4.35). <https://www-users.cse.umn.edu/~saad/IterMethBook_2ndEd.pdf>
