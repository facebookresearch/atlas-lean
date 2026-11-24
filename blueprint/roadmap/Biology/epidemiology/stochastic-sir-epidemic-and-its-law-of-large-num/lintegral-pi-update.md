# Tonelli formula over a product law with one coordinate resampled

Let `ι` be a finite index set, `μ_i` a probability measure on a measurable space `α_i` for each
`i ∈ ι`, and `π = ⊗_{i ∈ ι} μ_i` the product measure on `∏_{i ∈ ι} α_i`. For every coordinate
`x ∈ ι` and every measurable function `G : ∏_i α_i → [0, ∞]`,

`∫ G(ξ) dπ(ξ) = ∫ (∫ G(ξ[x ↦ z]) dπ(ξ)) dμ_x(z)`,

where `ξ[x ↦ z]` agrees with `ξ` except at the coordinate `x`, where it takes the value `z`. The
integrals are Lebesgue integrals of nonnegative functions, with values in `[0, ∞]`, so no
integrability is needed. The formula follows from
[resampling one coordinate](pi-map-update.md) and Tonelli's theorem.
