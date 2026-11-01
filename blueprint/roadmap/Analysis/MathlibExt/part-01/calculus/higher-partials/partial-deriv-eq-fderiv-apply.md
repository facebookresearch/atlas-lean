---
article_id: af_063dceeab20db2134bb405ef
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.partialDeriv_eq_fderiv_apply
---

# Partial Deriv eq fderiv apply

A partial derivative is the Frechet derivative applied to the axis vector.

Proof: Differentiate the affine coordinate line `t ↦ x + t • Pi.single i 1` and compose with `f`
by the chain rule `HasFDerivAt.comp_hasDerivAt`.

## Depends on

- [Partial Deriv](partial-deriv.md)

## Sources

- [MathlibExt, MathlibExt.Analysis.Calculus.HigherPartials](../../../../../../sources/v2/MathlibExt.md)
- `Mathlib/docs/undergrad.yaml`, section `Multivariable calculus` / `Differential calculus`, entry `partial derivatives` (unmapped); W. Rudin, Principles of Mathematical Analysis, 3rd ed., Ch. 9.
