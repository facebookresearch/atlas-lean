# Quantitative separation for the GTR pair-site MLE

Let `Θ` be a compact metric space. Let `ι` be a finite set of states and let `π`, `s` and `t` give
each parameter `θ` base frequencies `π θ : ι → ℝ`, exchangeabilities `s θ` (a real `ι × ι` matrix)
and a branch length `t θ > 0`, with every `(π θ, s θ)` in the
[GTR parameter domain](../gtr-identifiability-and-estimation/identifiability-of-the-gtr-model/is-gtrparam.md): `π θ i > 0`,
`∑_i π θ i = 1`, `s θ` symmetric and `s θ i j > 0` for `i ≠ j`. Write `law θ` for the
[pair-site law](gtr-law.md) of `θ`, assumed continuous in `θ`, and `C` for the
[identified class](gtr-class.md) of `θ₀`: the parameters `θ` with `π θ = π θ₀` and
`t θ · s θ i j = t θ₀ · s θ₀ i j` for all `i ≠ j`. For every `ε > 0` there is `η > 0` such that, for
all frequencies `f : ι × ι → ℝ` at sup distance less than `η` from `law θ₀`, every maximizer `θ̂` of
the [log-likelihood criterion](log-lik.md) `θ ↦ L(f, θ)` of the pair-site model satisfies
`d(θ̂, C) < ε`, where `d(θ, C) = inf_{θ' ∈ C} d(θ, θ')`.
