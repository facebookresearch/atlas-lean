# Henderson's mixed-model equations give the GLS estimator and the BLUP

For positive
definite `K`, `σ_g² > 0` and `X` of full column rank, `(β, g)` solves the mixed-model equations
iff `β = β̂` and `g = σ_g² K V⁻¹ (y - X β̂)`. This is the specialization of
`MixedModel.isMMESolution_iff_gls` to `Z = 1`, `G = σ_g² K`, `R = σ_e² I`; the generic
theorem gives `β = glsMatrix X V *ᵥ y` and `g = G V⁻¹ (y - X β̂)`, which are `Model.gls`
and `Model.blup` by the two conversion lemmas below.
