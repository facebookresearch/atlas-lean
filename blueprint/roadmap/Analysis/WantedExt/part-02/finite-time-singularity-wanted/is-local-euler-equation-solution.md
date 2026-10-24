---
article_id: af_f0a241408da7e8ad12634b72
declaration: structure
origin: cited
statement: formalized
lean: MathlibExt.Analysis.FiniteTimeSingularityWanted.FiniteTimeSingularity.IsLocalEulerEquationSolution
---

# Is Local Euler Equation Solution

We say that `u` is a local solution to the incompressible Euler equation up to time `T`,
with pressure `p` and initial vector field `u₀`, if `u` and `p` are continuously differentiable,
`∂ₜ u + (u ·∇ₓ u) + ∇ₓ p = 0` and `div u = 0` on `ℝ³ × (0,T)` and `u|ₜ₌₀ = u₀`.

## Depends on

This node has no prerequisites.

## Sources

- [WantedExt, WantedExt.Analysis.FiniteTimeSingularityWanted](../../../../../sources/v2/WantedExt.md)
