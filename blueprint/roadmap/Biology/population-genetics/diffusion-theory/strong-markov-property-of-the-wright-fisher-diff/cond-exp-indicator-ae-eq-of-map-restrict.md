# Conditional expectation from a conditional law, on an event

Let `μ` be a finite measure on a measurable space `(Ω, 𝓜)`, `𝒢 ⊆ 𝓜` a sub-σ-algebra, `κ` a Markov
kernel from `[0, 1]` to a measurable space `β`, `V : Ω → β` measurable, `W : Ω → [0, 1]`
`𝒢`-measurable and `S ∈ 𝒢`. Suppose that for every `A ∈ 𝒢` the image under `V` of the restriction
`μ|_{S ∩ A}` of `μ` to `S ∩ A` is `∫ κ(w, ·) ν_A(dw)`, where `ν_A` is the image of `μ|_{S ∩ A}`
under `W`; these measures have total mass `μ(S ∩ A)` and are not normalized. Then for every bounded
measurable `F : β → ℝ`, the conditional expectation under `μ` satisfies
`μ[1_S F(V) | 𝒢] = 1_S ∫ F(y) κ(W, dy)` `μ`-almost everywhere.
