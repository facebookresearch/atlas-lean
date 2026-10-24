---
article_id: af_f76ae57242a5bb8f7ae0e438
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MathlibExt.LinearAlgebra.TriangularizationWanted.exists_basis_upperTriangular_toMatrix
---

# Exists basis upper Triangular to Matrix

An endomorphism whose characteristic polynomial splits is triangularizable: there is a basis
in which its matrix is upper triangular.

Proof: induction on dimension. An eigenvector spans an invariant line, the induced map on the
quotient has split minimal polynomial (it divides that of `f`), and a triangularizing basis of the
quotient lifts, together with the eigenvector, to one of `V` (`Module.Basis.sumQuot`). This is the
eigenvector-deflation induction of the proof of Schur's theorem in R. A. Horn and C. R. Johnson,
Matrix Analysis, 2nd ed., Cambridge University Press (2013), Theorem 2.3.1, without unitarity.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.LinearAlgebra.Triangularization](../../../../sources/v2/MathlibExt.md)
- Mathlib `docs/undergrad.yaml`, Linear algebra / Structure theory of endomorphisms / triangularization; S. Axler, Linear Algebra Done Right, 4th ed., Springer (2024), Theorem 5.41.
