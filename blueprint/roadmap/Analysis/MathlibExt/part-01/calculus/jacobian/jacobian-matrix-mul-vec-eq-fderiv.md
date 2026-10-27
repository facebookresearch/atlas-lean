---
article_id: af_51626abdc1ab2bf6be5943ce
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.jacobianMatrix_mulVec_eq_fderiv
---

# Jacobian Matrix mul Vec eq fderiv

The Jacobian matrix represents the Frechet derivative on coordinates.

Proof: The Jacobian is the matrix of `fderiv` (Wikipedia, "Jacobian matrix and determinant":
it represents the total derivative), by `jacobianMatrix_eq_toMatrix'_fderiv`; then use
`LinearMap.toMatrix'_mulVec`.

## Depends on

- [Jacobian Matrix](jacobian-matrix.md)

## Proof depends on

- [Jacobian Matrix eq to Matrix' fderiv](jacobian-matrix-eq-to-matrix-fderiv.md)

## Sources

- [MathlibExt, MathlibExt.Analysis.Calculus.Jacobian](../../../../../../sources/v2/MathlibExt.md)
- `Mathlib/docs/undergrad.yaml`, section `Multivariable calculus` / `Differential calculus`, entry `Jacobian matrix` (unmapped); W. Rudin, Principles of Mathematical Analysis, 3rd ed., Ch. 9.
