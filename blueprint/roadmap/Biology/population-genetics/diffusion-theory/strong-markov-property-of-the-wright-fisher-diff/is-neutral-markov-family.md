# Markov family for the neutral Wright–Fisher semigroup

Let `μ` be a measure on a measurable space `Ω`, `(𝒢_u)_{u ≥ 0}` a filtration and `Y` a process with
values in `[0, 1]`. Then `Y` is a Markov family for the
[neutral Wright–Fisher semigroup](../wright-fisher-semigroup-and-moment-duality/wf-semigroup.md) `T`
with respect to `(𝒢_u)` under `μ` if each `Y_u` is `𝒢_u`-measurable and, for all times `0 ≤ u ≤ v`,
every `A ∈ 𝒢_u` and every continuous `g : [0, 1] → ℝ`, `∫_A g(Y_v) dμ = ∫_A (T_{v - u} g)(Y_u) dμ`.
These are real integrals, the integral of a non-integrable function being `0`, which can happen for
an infinite measure even for bounded `g`; for a finite measure `μ` both integrands are bounded and
measurable, so both integrals are genuine.
