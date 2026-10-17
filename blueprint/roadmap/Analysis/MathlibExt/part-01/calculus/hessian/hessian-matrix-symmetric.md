---
article_id: af_43c0a594e2ce9a2549fe0841
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.hessianMatrix_symmetric
---

# Hessian Matrix symmetric

The Hessian of a `C^2` function is symmetric.

Proof: Rewrite the matrix entries as evaluations of the second Fréchet derivative and apply
Mathlib's Schwarz theorem `ContDiffAt.isSymmSndFDerivAt`, following Wikipedia's “Symmetry of
second derivatives”.

## Depends on

- [Hessian Matrix](hessian-matrix.md)

## Proof depends on

- [Hessian Matrix eq fderiv fderiv](hessian-matrix-eq-fderiv-fderiv.md)

## Sources

- [MathlibExt, MathlibExt.Analysis.Calculus.Hessian](../../../../../../sources/v2/MathlibExt.md)
- `Mathlib/docs/undergrad.yaml`, section `Multivariable calculus` / `Differential calculus`, entry `Hessian matrix` (unmapped); W. Rudin, Principles of Mathematical Analysis, 3rd ed., Theorem 9.41 (pp. 235–236).
