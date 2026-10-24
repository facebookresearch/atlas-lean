---
article_id: af_ab37097602b29a2685f7f843
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MathlibExt.Analysis.FunctionalAnalysis.MilmanPettisWanted.milman_pettis
---

# Milman Pettis

If `E` is a uniformly convex Banach space over `𝕜 = ℝ` or `ℂ`, then every continuous linear
functional on the dual `E →L[𝕜] 𝕜` is evaluation at some `x : E`, i.e. `∃ x, ∀ f, Φ f = f x`.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Banach Space](goldstine.md)

## Sources

- [MathlibExt, MathlibExt.Analysis.FunctionalAnalysis.MilmanPettis](../../../../../../sources/v2/MathlibExt.md)
- D. Milman, C. R. (Doklady) Acad. Sci. URSS 18 (1938) and B. Pettis, Duke Math. J. 1939, Milman-Pettis theorem that uniformly convex Banach spaces are reflexive; Clarkson uniform convexity 1936; Lean states `RCLike` uniformly convex complete case via double-dual evaluation surjectivity.
