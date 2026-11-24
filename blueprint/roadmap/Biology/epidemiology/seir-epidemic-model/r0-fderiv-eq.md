# For β ≥ 0, σ, γ > 0 and N ≠ 0, SEIR rate derivatives give R₀ = β / γ

Let `β ≥ 0`, `σ, γ > 0` and `N ≠ 0`. Let `F` be the matrix of the derivative at `E = I = 0` of the
[new-infection rates](new-infections.md) `(E, I) ↦ ℱ(N; E, I)` at the disease-free level `S = N`,
and `V` the matrix of the derivative at `E = I = 0` of the [transfer rates](transfers.md) `𝒱`. Then
the [basic reproduction number](../next-generation-matrix-and-the-basic-reproductio/r0.md) is

`R₀ = ρ(F V⁻¹) = β / γ`.

Both maps are differentiable at `E = I = 0`, with `F = [[0, β], [0, 0]]` and
`V = [[σ, 0], [-σ, γ]]` (rows listed in order), so the value is that of
[the SEIR next-generation matrix](r0-eq.md). For `N = 0` the convention `x / 0 = 0` makes `ℱ`
identically zero, hence `F = 0` and `R₀ = 0`.
