# A nonnegative inverse of I − B forces ρ(B) < 1

Let $B$ be a real $n \times n$ matrix with nonnegative entries, with the convention that the spectral radius of the empty matrix ($n = 0$) is $0$. Then $\rho(B) < 1$ if and only if $I - B$ is nonsingular and $(I - B)^{-1}$ has nonnegative entries.

For $n = 0$ both sides hold. For $n \ge 1$, the forward direction is the Neumann series $(I - B)^{-1} = \sum_{k \ge 0} B^k$. For the converse, a nonnegative eigenvector $u$ for the eigenvalue $\rho(B)$ gives $(I - B)^{-1} u = u/(1 - \rho(B))$, and the left side is a nonzero nonnegative vector, so $1 - \rho(B) > 0$.

## Proof depends on

- [Neumann series](../../../../LinearAlgebra/special-matrices/m-matrices-and-hurwitz-stability/nonsingular-m-matrices/inv-one-sub-nonneg.md)
- [Perron eigenvector of a nonnegative matrix](perron-eigenvector-of-a-nonnegative-matrix.md)
- [I − B is invertible when ρ(B) < 1](../../../../LinearAlgebra/special-matrices/m-matrices-and-hurwitz-stability/nonsingular-m-matrices/is-unit-one-sub-of-spectral-radius-lt-on.md)

## Sources

- Y. Saad, *Iterative Methods for Sparse Linear Systems*, 2nd edition, SIAM, 2003, Section 1.10, Theorem 1.29 and its proof. <https://www-users.cse.umn.edu/~saad/IterMethBook_2ndEd.pdf>
