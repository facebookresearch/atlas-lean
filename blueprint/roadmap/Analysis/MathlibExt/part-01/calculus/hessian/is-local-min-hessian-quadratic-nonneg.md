---
article_id: af_3cd45cc52e4eac0b8cbcad1f
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.isLocalMin_hessian_quadratic_nonneg
---

# Is Local Min hessian quadratic nonneg

Second-derivative test, necessary direction: at a local minimizer of a
`C^2` function the Hessian quadratic form is nonnegative.

Proof: Restrict the function to the affine line in direction `v`, apply the necessary direction of
the one-variable second derivative test, then expand the second Fréchet derivative in the standard
basis. The one-variable step argues by contradiction as in the proof of the second-derivative
test in Wikipedia's “Derivative test”: a negative second derivative makes the first derivative
negative just right of the critical point, so the function decreases there.

## Depends on

- [Hessian Matrix](hessian-matrix.md)

## Proof depends on

- [Deriv deriv nonneg](deriv-deriv-nonneg.md)
- [Hessian Matrix eq fderiv fderiv](hessian-matrix-eq-fderiv-fderiv.md)

## Sources

- [MathlibExt, MathlibExt.Analysis.Calculus.Hessian](../../../../../../sources/v2/MathlibExt.md)
- `Mathlib/docs/undergrad.yaml`, section `Multivariable calculus` / `Differential calculus`, entry `Hessian matrix` (unmapped); W. Rudin, Principles of Mathematical Analysis, 3rd ed., Ch. 9.
