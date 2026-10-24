---
article_id: af_9bfb600f515cd68205ee4bb9
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MathlibExt.Geometry.Manifold.ImmersionOfInjectiveMFDerivWanted.immersionAt_of_injective_mfderiv
---

# Immersion At of injective mfderiv

A map between finite-dimensional manifolds without boundary over `ℝ` or `ℂ` that is `C^n` on a
neighbourhood of `x` and has injective differential at `x` is an immersion at `x`.

Proof: Choose a complement to the differential's range, apply the inverse function theorem to
the resulting product map in extended charts, and use its local inverse as a target chart.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Of injective mfderiv of closed Complemented range](of-injective-mfderiv-of-closed-complemen.md)

## Sources

- [MathlibExt, MathlibExt.Geometry.Manifold.ImmersionOfInjectiveMFDeriv](../../../../../../sources/v2/MathlibExt.md)
- Mathlib `Mathlib/Geometry/Manifold/Immersion.lean` TODO (finite-dimensional injective-`mfderiv` criterion); J. Lee, Introduction to Smooth Manifolds, 2nd ed., Ch. 4.
