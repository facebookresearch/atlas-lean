---
article_id: af_ce7c27a26a457695d7bd05a1
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MathlibExt.Analysis.FunctionalAnalysis.RieszThorinWanted.riesz_thorin
---

# Riesz thorin

For finite `ι, κ` with counting measure, if `T : (ι → ℂ) →ₗ[ℂ] (κ → ℂ)` has `ℓ^{p₀} → ℓ^{q₀}`
bound `M₀` and `ℓ^{p₁} → ℓ^{q₁}` bound `M₁` and `1/p = (1-θ)/p₀ + θ/p₁`, `1/q = (1-θ)/q₀ + θ/q₁`
with `θ ∈ [0, 1]`, then `eLpNorm (T f) q ≤ (M₀^(1-θ) * M₁^θ) * eLpNorm f p` for all `f`. Source:
M. Riesz, Sur les maxima des formes bilinéaires et sur les fonctionnelles linéaires,
Acta Math. 49 (1927), 465–497, DOI 10.1007/BF02564121; and G. O. Thorin, Convexity theorems
generalizing those of M. Riesz and Hadamard with some applications,
Comm. Sem. Math. Univ. Lund 9 (1948), 1–58, Riesz-Thorin interpolation theorem; Stein-Shakarchi
Complex interpolation; Lean states finite counting-measure complex `→ₗ[ℂ]` form with explicit
interpolation identities `p⁻¹=(1-θ)p₀⁻¹+θp₁⁻¹` and bound `M₀^(1-θ)M₁^θ`.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Riesz thorin finite](riesz-thorin-finite.md)

## Sources

- [MathlibExt, MathlibExt.Analysis.FunctionalAnalysis.RieszThorin](../../../../../../../sources/v2/MathlibExt.md)
