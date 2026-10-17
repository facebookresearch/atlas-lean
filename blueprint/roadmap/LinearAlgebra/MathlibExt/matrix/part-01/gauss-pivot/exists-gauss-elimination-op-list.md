---
article_id: af_cb4ecc22478574d59b4d0764
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MathlibExt.LinearAlgebra.Matrix.GaussPivotWanted.exists_gauss_elimination_opList
---

# Exists gauss elimination op List

Gaussian elimination with arbitrary nonzero row pivots admits an endpoint factorization into a
row permutation and a list of unit lower-triangular row operations whose product reaches row
echelon form. This records the factorization, not the intermediate matrices of an algorithm trace.

Proof: Induct on the columns after transporting the index orders to `Fin`; a nonzero first column
uses a row pivot and recurses on the lower-right block. Package the resulting single unit
lower-triangular matrix as a singleton list (forward elimination to row echelon form,
https://en.wikipedia.org/wiki/Gaussian_elimination).

## Depends on

This node has no prerequisites.

## Proof depends on

- [Exists unit Lower Triangular mul submatrix is Row Echelon](exists-unit-lower-triangular-mul-submatr.md)

## Sources

- [MathlibExt, MathlibExt.LinearAlgebra.Matrix.GaussPivot](../../../../../../sources/v2/MathlibExt.md)
- Mathlib `docs/undergrad.yaml`, Numerical Analysis / Solving systems of linear inequalities / Gauss's pivot; L. N. Trefethen and D. Bau, Numerical Linear Algebra, SIAM (1997), Lectures 20-21.
