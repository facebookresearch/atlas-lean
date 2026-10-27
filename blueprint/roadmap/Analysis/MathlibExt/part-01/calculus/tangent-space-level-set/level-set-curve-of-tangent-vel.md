---
article_id: af_50fc3bcd47204bf049fb5ac2
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.levelSet_curve_of_tangent_vel
---

# Level Set curve of tangent vel

Every kernel vector is tangent to a regular level set: at a point where
the Frechet derivative is surjective, each `v` with `fderiv = 0` is the
velocity of a curve staying in the level set.

Proof: Use the implicit function theorem to construct a local curve tangent to the kernel vector,
then compose it with a bounded arctangent reparametrization to obtain a curve on all of `ℝ`
(implicit function theorem, Banach space version:
https://en.wikipedia.org/wiki/Implicit_function_theorem).

## Depends on

This node has no prerequisites.

## Proof depends on

- [Exists level Set curve](exists-level-set-curve.md)

## Sources

- [MathlibExt, MathlibExt.Analysis.Calculus.TangentSpaceLevelSet](../../../../../../sources/v2/MathlibExt.md)
- `Mathlib/docs/undergrad.yaml`, section `Multivariable calculus` / `Submanifolds of R^n`, entry `tangent space` (unmapped); J. M. Lee, Introduction to Smooth Manifolds, 2nd ed., Theorem 5.12.
