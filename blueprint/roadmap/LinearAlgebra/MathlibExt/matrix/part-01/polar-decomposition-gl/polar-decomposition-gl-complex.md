---
article_id: af_d3ec8aff11912cba1e2c6d10
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MathlibExt.LinearAlgebra.Matrix.PolarDecompositionGLWanted.polar_decomposition_gl_complex
---

# Polar decomposition gl complex

Polar decomposition in `GL(n, ℂ)`: every invertible complex matrix is uniquely the product of
a unitary matrix and a positive-definite Hermitian matrix.

Proof: Specialize `Matrix.exists_unique_unitaryGroup_posDef_of_isUnit_det` to `ℂ` and unbundle
its unitary witness. The generic proof takes `P` to be the CFC square root of `Aᴴ * A` and
`U = A * P⁻¹`, the construction in Wikipedia, "Polar decomposition".

## Depends on

This node has no prerequisites.

## Proof depends on

- [Exists unique unitary Group pos Def of is Unit det](../factorizations/polar/exists-unique-unitary-group-pos-def-of-i.md)

## Sources

- [MathlibExt, MathlibExt.LinearAlgebra.Matrix.PolarDecompositionGL](../../../../../../sources/v2/MathlibExt.md)
- Mathlib `docs/undergrad.yaml`, Bilinear and Quadratic Forms Over a Vector Space / Endomorphisms / polar decompositions in GL(n, ℂ); R. A. Horn and C. R. Johnson, Matrix Analysis, 2nd ed., Cambridge University Press (2013), Theorem 7.3.1.
