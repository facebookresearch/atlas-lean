# GTR pair-site consistency in measure from convergent frequencies

Let `Θ` be a compact metric space. Let `ι` be a finite set of states and let `π`, `s` and `t` give
each parameter `θ` base frequencies `π θ : ι → ℝ`, exchangeabilities `s θ` (a real `ι × ι` matrix)
and a branch length `t θ > 0`, with every `(π θ, s θ)` in the
[GTR parameter domain](../identifiability-of-the-gtr-model/is-gtrparam.md): `π θ i > 0`,
`∑_i π θ i = 1`, `s θ` symmetric and `s θ i j > 0` for `i ≠ j`. Write `law θ` for the
[pair-site law](gtr-law.md) of `θ`, assumed continuous in `θ`, and `C` for the
[identified class](gtr-class.md) of `θ₀`: the parameters `θ` with `π θ = π θ₀` and
`t θ · s θ i j = t θ₀ · s θ₀ i j` for all `i ≠ j`. Let `P` be any measure on `Ω`. If frequency
estimates `freq n` converge to `law θ₀` in `P`-measure, for the sup distance on `ι × ι → ℝ`, then
every [maximum-likelihood estimator](is-mle.md) `est` for the pair-site model and `freq` satisfies,
for every `ε > 0`, `P {ω : d(est n ω, C) ≥ ε} → 0` as `n → ∞`, where
`d(θ, C) = inf_{θ' ∈ C} d(θ, θ')`. The estimator need not be measurable: `P` of a set that is not
measurable is its outer measure. For a probability measure `P` this is consistency in probability.
