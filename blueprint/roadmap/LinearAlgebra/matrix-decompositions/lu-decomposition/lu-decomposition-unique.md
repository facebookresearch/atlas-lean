# Uniqueness of the LU decomposition

Let $K$ be a field and $A$ an invertible $n \times n$
matrix over $K$. Suppose $A = L_1 U_1 = L_2 U_2$, where $L_1$ and $L_2$ are lower triangular
$n \times n$ matrices over $K$ with every diagonal entry equal to $1$, and $U_1$ and $U_2$ are
upper triangular $n \times n$ matrices over $K$. Then $L_1 = L_2$ and $U_1 = U_2$.

Proof: Move the invertible triangular factors across the equality, then use the triangular inverse
and diagonal formulas to show the resulting matrix is the identity. The statement is the
uniqueness half of Wikipedia, "LU decomposition", section "Existence and uniqueness".

## Sources

- Mathlib `docs/undergrad.yaml`, Numerical Analysis / Solving systems of linear inequalities / LU decomposition; L. N. Trefethen and D. Bau, Numerical Linear Algebra, SIAM (1997), Lecture 20.
