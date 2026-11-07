# One pivot step of Gaussian elimination

Let $K$ be a field and let $A$ be a matrix over $K$
whose rows and columns are indexed by finite linearly ordered sets. Let $r$ and $i_0$ be row
indices and $j$ a column index with $A_{i_0 j} \ne 0$, and let $A'$ be the matrix obtained from
$A$ by exchanging rows $r$ and $i_0$. Then there is a square matrix $P$ over $K$ indexed by the
row indices, lower triangular with every diagonal entry equal to $1$, such that
$(P A')_{i j} = 0$ for every row $i > r$.

The row $i_0$ may be any row with a nonzero entry in column $j$; this is not
magnitude-maximizing partial pivoting.

Proof: Use an entrywise unit lower-triangular matrix whose pivot column contains the elimination
coefficients, then evaluate the matrix product as a finite sum (row operations of type 3,
https://en.wikipedia.org/wiki/Gaussian_elimination).

## Sources

- Mathlib `docs/undergrad.yaml`, Numerical Analysis / Solving systems of linear inequalities / Gauss's pivot; L. N. Trefethen and D. Bau, Numerical Linear Algebra, SIAM (1997), Lectures 20-21.
