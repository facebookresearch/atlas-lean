# Joint law with the past

Let `μ` be a finite measure on a measurable space `Ω`, `(𝒢_u)_{u ≥ 0}` a filtration and `Y` a
[Markov family](is-neutral-markov-family.md) for the neutral Wright–Fisher semigroup with respect to
`(𝒢_u)` under `μ`. Let `0 ≤ u ≤ v`, let `Z : Ω → β` be a `𝒢_u`-measurable map into a measurable
space `β` and `φ : β → [0, 1]` a measurable map with `φ(Z(ω)) = Y_u(ω)` for every `ω`, and let
`A ∈ 𝒢_u`. Then the joint law of `(Z, Y_v)` under `μ` restricted to `A` gives each measurable
rectangle `B × C` the mass `∫_B K_{v - u}(φ(z), C) ν(dz)`, where `ν` is the law of `Z` under `μ`
restricted to `A` and `K` is the
[neutral Wright–Fisher kernel](../construction-of-the-neutral-wright-fisher-diffus/neutral-kernel.md).
