---
article_id: af_275d7aea41118367d5527bcc
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MathlibExt.LinearAlgebra.TriangularizationWanted.exists_upperTriangular_similar_of_splits
---

# Exists upper Triangular similar of splits

A square matrix whose characteristic polynomial splits is similar to an upper-triangular
matrix.

Proof: apply `exists_basis_upperTriangular_toMatrix` to `Matrix.toLin` of the matrix and
conjugate by the change-of-basis matrix from the standard basis.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Exists basis upper Triangular to Matrix](exists-basis-upper-triangular-to-matrix.md)

## Sources

- [MathlibExt, MathlibExt.LinearAlgebra.Triangularization](../../../../sources/v2/MathlibExt.md)
- Mathlib `docs/undergrad.yaml`, Linear algebra / Structure theory of endomorphisms / triangularization; R. A. Horn and C. R. Johnson, Matrix Analysis, 2nd ed., Cambridge University Press (2013), Theorem 2.3.1.
