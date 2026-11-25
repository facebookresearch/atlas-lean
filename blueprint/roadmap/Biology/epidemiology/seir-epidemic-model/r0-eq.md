# For β ≥ 0 and σ, γ > 0, the SEIR R₀ = ρ(F V⁻¹) equals β / γ

Let `β ≥ 0` and `σ, γ > 0`, and let `F = [[0, β], [0, 0]]` and `V = [[σ, 0], [-σ, γ]]` be the
Jacobians of the [new-infection rates](has-fderiv-at-new-infections.md) and of the
[transfer rates](has-fderiv-at-transfers.md) at the disease-free equilibrium when `N ≠ 0` (rows
listed in order). Then `V` is invertible, with `V⁻¹ = [[1/σ, 0], [1/γ, 1/γ]]`, the next-generation
matrix is `F V⁻¹ = [[β/γ, β/γ], [0, 0]]`, with eigenvalues `β/γ` and `0`, and the
[basic reproduction number](../next-generation-matrix-and-the-basic-reproductio/r0.md), its spectral
radius, is

`R₀ = ρ(F V⁻¹) = β / γ`.

It does not depend on `σ`: the latent period delays infections but, with no deaths in the latent
class, does not change `R₀`.
