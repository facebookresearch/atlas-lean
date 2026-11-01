---
article_id: af_3d84f6262bf181e2263e2cc3
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MathlibExt.Geometry.Manifold.SubmersionOfSurjectiveMFDerivWanted.submersionAt_of_surjective_mfderiv
---

# Submersion At of surjective mfderiv

A map between finite-dimensional manifolds without boundary over `ℝ` or `ℂ` that is `C^n` on a
neighbourhood of `x` and has surjective differential at `x` is a submersion at `x`.

Proof: Split the surjective derivative, augment the map by its kernel coordinate, and apply the
inverse function theorem to obtain charts in which the map is the first projection.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Of surjective mfderiv](of-surjective-mfderiv.md)

## Sources

- [MathlibExt, MathlibExt.Geometry.Manifold.SubmersionOfSurjectiveMFDeriv](../../../../../../sources/v2/MathlibExt.md)
- Mathlib `Mathlib/Geometry/Manifold/Submersion.lean` TODO (finite-dimensional surjective-`mfderiv` criterion); J. Lee, Introduction to Smooth Manifolds, 2nd ed., Ch. 4.
