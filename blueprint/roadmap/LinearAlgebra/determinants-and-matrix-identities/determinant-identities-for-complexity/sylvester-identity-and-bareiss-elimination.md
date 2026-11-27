# Sylvester's determinant identity and Bareiss fraction-free elimination

Let $A$ be an $n\times n$ matrix over a commutative ring and, for indices with $k< i\le n$ and $k< j\le n$, let $a^{(k)}_{ij}$ be the determinant of the $(k+1)\times(k+1)$ submatrix with rows $1,\dots,k,i$ and columns $1,\dots,k,j$ (so $a^{(0)}_{ij}=a_{ij}$). Then Sylvester's identity holds:

$$
a^{(k+1)}_{ij}\,a^{(k-1)}_{kk}=a^{(k)}_{k+1,k+1}a^{(k)}_{ij}-a^{(k)}_{i,k+1}a^{(k)}_{k+1,j}\quad(\text{with } a^{(-1)}_{00}=1).
$$

Consequently, when the leading principal minors $a^{(k-1)}_{kk}$ ($1 \le k < n$) are not zero divisors (over $\mathbb{Z}$: nonzero; otherwise rows are exchanged first), Bareiss's fraction-free Gaussian elimination, which updates entries by this formula with exact division by the previous pivot, stays within the ring (over $\mathbb{Z}$ all intermediate values are minors of $A$, hence of polynomial bit length) and computes $\det A=a^{(n-1)}_{nn}$.

## Proof sketch

Apply the Desnanot–Jacobi (Schur complement) identity to the bordered $(k+2)\times(k+2)$ submatrix with rows $1,\dots,k+1,i$ and columns $1,\dots,k+1,j$.

## Depends on

- [Leibniz formula for the determinant](../determinants-of-matrices/leibniz-formula/det-apply.md)
- [Carroll (Desnanot–Jacobi) identity](../desnanot-jacobi-identity/carroll-identity.md)

## Sources

- Alexander Schrijver, "Theory of Linear and Integer Programming", John Wiley & Sons, 1986.
- E. H. Bareiss, "Sylvester's identity and multistep integer-preserving Gaussian elimination", Mathematics of Computation 22(103), 1968.
