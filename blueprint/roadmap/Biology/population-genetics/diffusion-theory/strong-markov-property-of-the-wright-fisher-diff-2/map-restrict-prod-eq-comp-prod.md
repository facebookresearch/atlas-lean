# Joint law with the past

Let `κ = (κ_t)_{t ≥ 0}` be a family of Markov kernels on `[0, 1]`, `μ` a finite measure on a
measurable space `Ω`, `(𝒢_u)_{u ≥ 0}` a filtration and `Y` a
[Markov family for `κ`](is-kernel-markov-family.md) with respect to `(𝒢_u)` under `μ`: each `Y_u` is
a `𝒢_u`-measurable map into `[0, 1]`, and `∫_A g(Y_v) dμ = ∫_A ∫ g(y) κ_{v - u}(Y_u, dy) dμ` for all
times `0 ≤ u ≤ v`, every `A ∈ 𝒢_u` and every continuous `g : [0, 1] → ℝ`. Let `0 ≤ u ≤ v`, let
`Z : Ω → β` be a `𝒢_u`-measurable map into a measurable space `β` and `φ : β → [0, 1]` a measurable
map with `φ(Z(ω)) = Y_u(ω)` for every `ω`, and let `A ∈ 𝒢_u`. Then the image of `μ|_A` under
`(Z, Y_v)` gives each measurable rectangle `B × C` the mass `∫_B κ_{v - u}(φ(z), C) ν(dz)`, where
`ν` is the image of `μ|_A` under `Z`. Here `μ|_A` is the restriction of `μ` to `A`; an image measure
of `μ|_A` has total mass `μ(A)` and is not normalized (it is the zero measure when `μ(A) = 0`).
