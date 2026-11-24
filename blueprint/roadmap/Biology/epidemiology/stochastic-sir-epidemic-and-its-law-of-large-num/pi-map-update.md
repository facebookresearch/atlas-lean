# Resampling one coordinate preserves a product of probability laws

Let `ι` be a finite index set and, for each `i ∈ ι`, let `μ_i` be a probability measure on a
measurable space `α_i`; let `π = ⊗_{i ∈ ι} μ_i` be the product measure on `∏_{i ∈ ι} α_i`. For a
point `ξ` of the product, a coordinate `x ∈ ι` and `z ∈ α_x`, let `ξ[x ↦ z]` be the point that
agrees with `ξ` except at `x`, where it takes the value `z`. Then, for every `x ∈ ι`, the map
`(z, ξ) ↦ ξ[x ↦ z]` pushes the product measure `μ_x ⊗ π` on `α_x × ∏_i α_i` forward to `π`.

In words: drawing `ξ` from `π` and replacing its coordinate `x` by an independent draw from the
marginal `μ_x` does not change the law `π`.
