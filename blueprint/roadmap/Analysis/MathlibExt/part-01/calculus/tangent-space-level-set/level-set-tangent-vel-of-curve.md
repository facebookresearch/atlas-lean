---
article_id: af_b727788f3bf63aa1a17d4012
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.levelSet_tangent_vel_of_curve
---

# Level Set tangent vel of curve

Tangent vectors to a Euclidean level set lie in the kernel: if a curve
through `x` stays in the level set `{f = c}` with velocity `v`, then the
Frechet derivative kills `v`.

Proof: Apply the chain rule to `f ∘ γ`, then compare its derivative with that of the constant
function determined by the level-set equation.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.Analysis.Calculus.TangentSpaceLevelSet](../../../../../../sources/v2/MathlibExt.md)
- `Mathlib/docs/undergrad.yaml`, section `Multivariable calculus` / `Submanifolds of R^n`, entry `tangent space` (unmapped); J. M. Lee, Introduction to Smooth Manifolds, 2nd ed., Theorem 5.12; stable ref https://en.wikipedia.org/wiki/Tangent_space.
