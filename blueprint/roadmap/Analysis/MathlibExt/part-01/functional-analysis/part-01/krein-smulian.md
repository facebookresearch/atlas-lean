---
article_id: af_537b7b2d53e547460c002144
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MathlibExt.Analysis.FunctionalAnalysis.BanachSpaceWanted.krein_smulian
---

# Krein Smulian

For a Banach space over `ℝ` or `ℂ` and `C ⊆ WeakDual 𝕜 E` convex over `ℝ`, `C` is weak-star closed
iff for every `r > 0` the intersection with each norm ball is weak-star closed. Source: M. Krein
and V. Smulian, Ann. of Math. 41 (1940) 556-583; Dunford-Schwartz I; Lean states `RCLike` Banach
case with `Convex ℝ s` and closedBall intersections.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.Analysis.FunctionalAnalysis.KreinSmulian](../../../../../../sources/v2/MathlibExt.md)
