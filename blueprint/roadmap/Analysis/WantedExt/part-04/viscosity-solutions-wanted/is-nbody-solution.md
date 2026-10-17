---
article_id: af_2474bc53f6b48319fdd1f401
declaration: structure
origin: cited
statement: formalized
lean: MathlibExt.Analysis.ViscositySolutionsWanted.ViscositySolutions.IsNBodySolution
---

# Is NBody Solution

Given masses `m : ℝᴺ`, we say that `x : ℝ → Eᴺ` is a solution to the N-body problem if
`x ∈ C²((0,∞))`, `x` is continuous at `0`, and for all `t > 0`, `x'' = ∇ₘ U(x(t))`.

## Depends on

This node has no prerequisites.

## Sources

- [WantedExt, WantedExt.Analysis.ViscositySolutionsWanted](../../../../../sources/v2/WantedExt.md)
