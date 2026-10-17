---
article_id: af_bf06e523a8691d4f1efbf0e0
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MathlibExt.Analysis.FunctionalAnalysis.RosenthalL1Wanted.rosenthal_l1
---

# Rosenthal l1

Every bounded sequence `x` in a Banach space over `𝕜 = ℝ` or `ℂ` has a strictly increasing
subsequence `φ` such that `x ∘ φ` is either weakly Cauchy (`f (x (φ n))` Cauchy for every `f : E
→L[𝕜] 𝕜`) or has a uniform `ℓ¹` lower bound. Source: H. P. Rosenthal,
A Characterization of Banach Spaces Containing l1, PNAS 71 (1974), 2411–2413,
DOI 10.1073/pnas.71.6.2411, ℓ¹ dichotomy theorem; Bourgain et al., extensions; Lean states
`RCLike` Banach bounded `Set.range` dichotomy with `StrictMono φ` and `HasUniformL1LowerBound`
defined via `ℕ →₀ 𝕜` finitely supported coefficients.

Proof: We use the Nash-Williams/Galvin-Prikry Ramsey route, following Rosenthal's 1974 theorem,
Albiac and Kalton, Sections 10.1–10.2, and Farahat's 1974 proof.

## Depends on

- [Has Uniform L1 Lower Bound](has-uniform-l1-lower-bound.md)

## Sources

- [MathlibExt, MathlibExt.Analysis.FunctionalAnalysis.RosenthalL1](../../../../../../../sources/v2/MathlibExt.md)
