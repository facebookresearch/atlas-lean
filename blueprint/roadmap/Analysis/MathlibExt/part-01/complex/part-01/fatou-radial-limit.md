---
article_id: af_0ab2c52f80d70265dad4abca
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MathlibExt.Analysis.Complex.FatouRadialWanted.fatou_radial_limit
---

# Fatou Radial

If `f : ℂ → ℂ` is holomorphic on `ball (0:ℂ) 1` and uniformly bounded there, then for
Lebesgue-a.e. `θ ∈ [0, 2π]` the radial limit `f (r * exp (Iθ)) → L` exists in `ℂ` as `r → 1-` via
`Filter.Tendsto` with `𝓝[<] 1`. Source: Fatou radial limit theorem for H∞, P. Fatou, Acta Math. 30
(1906); see Rudin, Real and Complex Analysis, Bounded Analytic Functions; Lean is bounded
holomorphic on ball 0 1 with a.e. radial limit via volume.restrict Icc 0 (2π) and 𝓝[<] 1.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.Analysis.Complex.FatouRadial](../../../../../../sources/v2/MathlibExt.md)
