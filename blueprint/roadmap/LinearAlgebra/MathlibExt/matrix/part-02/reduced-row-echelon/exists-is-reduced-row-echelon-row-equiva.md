---
article_id: af_900862261571640b82de542f
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MathlibExt.LinearAlgebra.Matrix.ReducedRowEchelonWanted.exists_isReducedRowEchelon_rowEquivalent
---

# Exists is Reduced Row Echelon row Equivalent

Every matrix over a field is row-equivalent to a matrix in reduced row echelon form.

Proof: Choose pivot columns greedily (columns outside the span of the earlier ones), extend them
to a basis of `m → K` whose order matches the rows, and take `R` to be the coordinate matrix of the
columns of `A` in that basis and `P` the matrix of the coordinate map.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.LinearAlgebra.Matrix.ReducedRowEchelon](../../../../../../sources/v2/MathlibExt.md)
- Mathlib `docs/undergrad.yaml`, Linear algebra / Matrices / row-reduced matrices; G. Strang, Introduction to Linear Algebra, 6th ed., Wellesley-Cambridge Press (2023), Section 2.2.
