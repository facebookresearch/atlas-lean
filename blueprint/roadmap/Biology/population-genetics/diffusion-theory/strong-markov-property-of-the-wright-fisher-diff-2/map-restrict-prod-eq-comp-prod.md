# Joint law with the past

Let `κ = (κ_t)_{t ≥ 0}` be a family of Markov kernels on `[0, 1]`, `μ` a finite measure on a
measurable space `Ω`, `(𝒢_u)_{u ≥ 0}` a filtration and `Y` a
[Markov family for `κ`](is-kernel-markov-family.md) with respect to `(𝒢_u)` under `μ`. Let
`0 ≤ u ≤ v`, let `Z : Ω → β` be a `𝒢_u`-measurable map into a measurable space `β` and
`φ : β → [0, 1]` a measurable map with `φ(Z(ω)) = Y_u(ω)` for every `ω`, and let `A ∈ 𝒢_u`. Then the
joint law of `(Z, Y_v)` under `μ` restricted to `A` gives each measurable rectangle `B × C` the mass
`∫_B κ_{v - u}(φ(z), C) ν(dz)`, where `ν` is the law of `Z` under `μ` restricted to `A`.
