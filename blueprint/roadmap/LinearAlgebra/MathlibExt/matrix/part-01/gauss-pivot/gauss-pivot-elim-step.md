---
article_id: af_85e9aeb1132f573fa9c35dd4
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MathlibExt.LinearAlgebra.Matrix.GaussPivotWanted.gauss_pivot_elim_step
---

# Gauss pivot elim step

One row-pivot step of Gaussian elimination: given any nonzero entry in column `j`, swap its row
to the pivot row `r` and clear the entries below it by a unit lower-triangular row operation.
This is arbitrary nonzero pivot selection, not magnitude-maximizing partial pivoting.

Proof: Use an entrywise unit lower-triangular matrix whose pivot column contains the elimination
coefficients, then evaluate the matrix product as a finite sum (row operations of type 3,
https://en.wikipedia.org/wiki/Gaussian_elimination).

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.LinearAlgebra.Matrix.GaussPivot](../../../../../../sources/v2/MathlibExt.md)
- Mathlib `docs/undergrad.yaml`, Numerical Analysis / Solving systems of linear inequalities / Gauss's pivot; L. N. Trefethen and D. Bau, Numerical Linear Algebra, SIAM (1997), Lectures 20-21.
