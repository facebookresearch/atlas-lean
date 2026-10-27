---
article_id: af_25cd5e479d4b0eb4cc8a3582
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.curve_length_eq_integral_norm_deriv
---

# Curve length eq integral norm deriv

Curve length as the integral of speed: a `C^1` curve on `[a, b]` has
variation (length) equal to the integral of the norm of its derivative.

Proof: Extend the within derivative by zero and identify its primitive's vector measure with the
corresponding density vector measure. Its variation is the integral of the norm, and ordinary and
within derivatives agree almost everywhere on the interval.

## Depends on

This node has no prerequisites.

## Proof depends on

- [E Variation On Icc eq of Real integral norm deriv Within](e-variation-on-icc-eq-of-real-integral-n.md)
- [Integral norm deriv eq integral norm deriv Within Icc](integral-norm-deriv-eq-integral-norm-der.md)

## Sources

- [MathlibExt, MathlibExt.Analysis.Calculus.CurveLength](../../../../../../sources/v2/MathlibExt.md)
- `Mathlib/docs/undergrad.yaml`, section `Multivariable calculus` / `Submanifolds of R^n`, entry `curve length` (unmapped); W. Rudin, Principles of Mathematical Analysis, 3rd ed., Ch. 6; stable ref https://en.wikipedia.org/wiki/Arc_length.
