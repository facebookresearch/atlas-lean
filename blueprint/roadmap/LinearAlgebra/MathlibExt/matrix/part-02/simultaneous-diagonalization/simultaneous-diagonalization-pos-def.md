---
article_id: af_ec7d9c8e45158138946ea7ad
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MathlibExt.LinearAlgebra.Matrix.SimultaneousDiagonalizationWanted.simultaneous_diagonalization_posDef
---

# Simultaneous diagonalization pos Def

Simultaneous diagonalization of two real quadratic forms with one positive-definite: for a
symmetric matrix `S` and a positive-definite matrix `P`, there is an invertible congruence
diagonalizing `S` while normalizing `P` to the identity.

Proof: Normalize `P` to the identity by a congruence built from its orthonormal eigenbasis, scaled
by the inverse square roots of its eigenvalues, then orthogonally diagonalize the transformed
symmetric matrix. This is the argument of Wikipedia's "Definite matrix", section "Simultaneous
diagonalization", with the eigenbasis scaling in place of a Cholesky factor.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Exists is Unit transpose mul mul eq one](exists-is-unit-transpose-mul-mul-eq-one.md)

## Sources

- [MathlibExt, MathlibExt.LinearAlgebra.Matrix.SimultaneousDiagonalization](../../../../../../sources/v2/MathlibExt.md)
- Mathlib `docs/undergrad.yaml`, Bilinear and Quadratic Forms Over a Vector Space / Endomorphisms / simultaneous diagonalization of two real quadratic forms, with one positive-definite; R. A. Horn and C. R. Johnson, Matrix Analysis, 2nd ed., Cambridge University Press (2013), Theorem 4.5.15.
