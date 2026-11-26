# Inverse-nonnegative Z-matrices have positive diagonal

Let $A$ be a real $n \times n$ matrix with $a_{ij} \le 0$ for $i \ne j$, nonsingular, with $A^{-1} \ge 0$ entrywise. Then $a_{ii} > 0$ for every $i$, so $A$ is an [M-matrix](m-matrix.md), and $\rho(I - D^{-1}A) < 1$ for its diagonal $D$. Condition 1 of the definition of an M-matrix is therefore implied by the other three.

## Depends on

- [M-matrix](m-matrix.md)

## Proof depends on

- [M-matrices are characterized by their Jacobi iteration matrices](m-matrix-iff-jacobi-spectral-radius-below-one.md)

## Sources

- Y. Saad, *Iterative Methods for Sparse Linear Systems*, 2nd edition, SIAM, 2003, Section 1.10, Theorem 1.32 and its proof from $(AA^{-1})_{ii} = 1$. <https://www-users.cse.umn.edu/~saad/IterMethBook_2ndEd.pdf>
