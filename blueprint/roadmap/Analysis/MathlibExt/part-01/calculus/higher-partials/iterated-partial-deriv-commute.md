---
article_id: af_ee2d7ccc891e0bd376a78cd4
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.iterated_partialDeriv_commute
---

# Iterated partial Deriv commute

Iterated partials commute for `C^2` functions (Clairaut's theorem).

Proof: Rewrite both iterated partials through the Fréchet bridge above, then apply Mathlib's
`ContDiffAt.isSymmSndFDerivAt`, Schwarz's theorem as stated in Wikipedia, "Symmetry of second
derivatives".

## Depends on

- [Partial Deriv](partial-deriv.md)

## Proof depends on

- [Partial Deriv partial Deriv eq fderiv fderiv](partial-deriv-partial-deriv-eq-fderiv-fd.md)

## Sources

- [MathlibExt, MathlibExt.Analysis.Calculus.HigherPartials](../../../../../../sources/v2/MathlibExt.md)
- `Mathlib/docs/undergrad.yaml`, section `Multivariable calculus` / `Differential calculus`, entry `k-th order partial derivatives` (unmapped); W. Rudin, Principles of Mathematical Analysis, 3rd ed., Theorem 9.41 (pp. 235–236).
