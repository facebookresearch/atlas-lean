# A Z-matrix is a nonsingular M-matrix if and only if its inverse is nonnegative

Let $A$ be a real $n \times n$ [Z-matrix](../../../../LinearAlgebra/special-matrices/m-matrices-and-hurwitz-stability/nonsingular-m-matrices/is-zmatrix.md), $a_{ij} \le 0$ for $i \ne j$. Then $A$ is a [nonsingular M-matrix](../../../../LinearAlgebra/special-matrices/m-matrices-and-hurwitz-stability/nonsingular-m-matrices/is-nonsingular-mmatrix.md), that is, every complex eigenvalue of $A$ has positive real part, if and only if $A$ is nonsingular and $A^{-1}$ has nonnegative entries.

For $n = 0$ both sides hold. For $n \ge 1$, the forward direction is the [inverse positivity of nonsingular M-matrices](../../../../LinearAlgebra/special-matrices/m-matrices-and-hurwitz-stability/nonsingular-m-matrices/inv-nonneg.md) with their [invertibility](../../../../LinearAlgebra/special-matrices/m-matrices-and-hurwitz-stability/nonsingular-m-matrices/is-unit.md). Conversely, take $s > \max_i a_{ii}$, so that $B = sI - A \ge 0$, and a nonzero nonnegative eigenvector $v$ of $B$ for $\rho(B)$; then $Av = (s - \rho(B))v$, so $v = (s - \rho(B)) A^{-1} v$ with $A^{-1} v \ge 0$ nonzero, which forces $s > \rho(B)$, and every eigenvalue $s - \mu$ of $A$, with $\mu$ an eigenvalue of $B$, has real part at least $s - \rho(B) > 0$.

## Depends on

- [Z-matrix](../../../../LinearAlgebra/special-matrices/m-matrices-and-hurwitz-stability/nonsingular-m-matrices/is-zmatrix.md)
- [Nonsingular M-matrix](../../../../LinearAlgebra/special-matrices/m-matrices-and-hurwitz-stability/nonsingular-m-matrices/is-nonsingular-mmatrix.md)

## Proof depends on

- [Inverse positivity of M-matrices](../../../../LinearAlgebra/special-matrices/m-matrices-and-hurwitz-stability/nonsingular-m-matrices/inv-nonneg.md)
- [Nonsingular M-matrices are invertible](../../../../LinearAlgebra/special-matrices/m-matrices-and-hurwitz-stability/nonsingular-m-matrices/is-unit.md)
- [Perron eigenvector of a nonnegative matrix](perron-eigenvector-of-a-nonnegative-matrix.md)

## Sources

- A. Berman and R. J. Plemmons, *Nonnegative Matrices in the Mathematical Sciences*, SIAM, 1994, Chapter 6, Theorem 2.3, the equivalence for Z-matrices of condition (G20) (every eigenvalue has positive real part), which the existing nonsingular M-matrix page takes as its definition, and condition (N38) (nonsingular with a nonnegative inverse). <https://doi.org/10.1137/1.9781611971262>
- Y. Saad, *Iterative Methods for Sparse Linear Systems*, 2nd edition, SIAM, 2003, Section 1.10, Definition 1.30 (M-matrices as nonsingular Z-matrices with positive diagonal and nonnegative inverse) and Theorem 1.32 (the positive diagonal follows from the other conditions). <https://www-users.cse.umn.edu/~saad/IterMethBook_2ndEd.pdf>
