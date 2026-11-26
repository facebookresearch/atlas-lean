# M-matrices are characterized by their Jacobi iteration matrices

Let $A$ be a real $n \times n$ matrix with $a_{ii} > 0$ for all $i$ and $a_{ij} \le 0$ for $i \ne j$, and let $D$ be its diagonal. Then $A$ is an [M-matrix](m-matrix.md) if and only if

$$\rho(I - D^{-1}A) < 1,$$

that is, exactly when the Jacobi iteration for $Ax = b$ converges for every right-hand side $b$ and every starting vector.

## Depends on

- [M-matrix](m-matrix.md)

## Proof depends on

- [A nonnegative inverse of I − B forces ρ(B) < 1](nonnegative-inverse-forces-spectral-radius-below-one.md)

## Related topics

- [Jacobi and Gauss–Seidel iterations](../jacobi-and-gauss-seidel-iteration-matrices.md)

## Sources

- Y. Saad, *Iterative Methods for Sparse Linear Systems*, 2nd edition, SIAM, 2003, Section 1.10, the argument after Definition 1.30 and Theorem 1.31 with its proof. <https://www-users.cse.umn.edu/~saad/IterMethBook_2ndEd.pdf>
