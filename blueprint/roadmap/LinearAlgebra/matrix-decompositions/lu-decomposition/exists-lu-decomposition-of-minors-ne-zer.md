# LU decomposition without pivoting

Let $K$ be a field and $A$ an $n \times n$ matrix over
$K$ whose leading principal minors are all nonzero: for every $k \le n$, the determinant of the
upper-left $k \times k$ block of $A$ is nonzero. Then $A = LU$ for some $n \times n$ matrices
$L$ and $U$ over $K$ such that $L$ is lower triangular with every diagonal entry equal to $1$ and
$U$ is upper triangular.

Proof: Induct on the dimension and extend the factorization of the leading principal block by a
bordered (Schur-complement) step. The statement is the existence half of Wikipedia, "LU
decomposition", section "Existence and uniqueness".

## Sources

- L. N. Trefethen and D. Bau, Numerical Linear Algebra, SIAM (1997), Lecture 20.
