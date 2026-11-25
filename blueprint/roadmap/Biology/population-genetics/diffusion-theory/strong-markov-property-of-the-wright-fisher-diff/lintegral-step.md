# Kernel form of the Markov property for nonnegative functions

Let `μ` be a finite measure on a measurable space `Ω`, `(𝒢_u)_{u ≥ 0}` a filtration and `Y` a
[Markov family](is-neutral-markov-family.md) for the
[neutral Wright–Fisher semigroup](../wright-fisher-semigroup-and-moment-duality/wf-semigroup.md) `T`
with respect to `(𝒢_u)` under `μ`: each `Y_u` is a `𝒢_u`-measurable map into `[0, 1]`, and
`∫_A g(Y_v) dμ = ∫_A (T_{v - u} g)(Y_u) dμ` for all times `0 ≤ u ≤ v`, every `A ∈ 𝒢_u` and every
continuous `g : [0, 1] → ℝ`. For all times `0 ≤ u ≤ v`, every `A ∈ 𝒢_u` and every measurable
`f : [0, 1] → [0, ∞]`, `∫_A f(Y_v) dμ = ∫_A ∫ f(y) K_{v - u}(Y_u, dy) dμ`, where `K` is the
[neutral Wright–Fisher kernel](../construction-of-the-neutral-wright-fisher-diffus/neutral-kernel.md).
