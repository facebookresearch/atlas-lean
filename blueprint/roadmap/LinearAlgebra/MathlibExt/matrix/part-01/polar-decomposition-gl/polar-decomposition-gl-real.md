---
article_id: af_2e8a14394f405d0e8449e65a
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MathlibExt.LinearAlgebra.Matrix.PolarDecompositionGLWanted.polar_decomposition_gl_real
---

# Polar decomposition gl real

Polar decomposition in `GL(n, ℝ)`: every invertible real matrix is uniquely the product of an
orthogonal matrix and a positive-definite symmetric matrix.

Proof: Specialize `Matrix.exists_unique_unitaryGroup_posDef_of_isUnit_det` to `ℝ`, where the
unitary group is the orthogonal group, and unbundle its unitary witness. The generic proof takes
`P` to be the CFC square root of `Aᴴ * A` and `U = A * P⁻¹`, the construction in Wikipedia,
"Polar decomposition".

## Depends on

This node has no prerequisites.

## Proof depends on

- [Exists unique unitary Group pos Def of is Unit det](../factorizations/polar/exists-unique-unitary-group-pos-def-of-i.md)

## Sources

- [MathlibExt, MathlibExt.LinearAlgebra.Matrix.PolarDecompositionGL](../../../../../../sources/v2/MathlibExt.md)
- Mathlib `docs/undergrad.yaml`, Bilinear and Quadratic Forms Over a Vector Space / Endomorphisms / polar decompositions in GL(n, ℝ); R. A. Horn and C. R. Johnson, Matrix Analysis, 2nd ed., Cambridge University Press (2013), Theorem 7.3.1.
