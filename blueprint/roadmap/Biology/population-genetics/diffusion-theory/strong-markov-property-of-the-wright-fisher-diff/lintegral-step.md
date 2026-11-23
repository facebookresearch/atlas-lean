# Kernel form of the Markov property for nonnegative functions

Let `μ` be a finite measure on a measurable space `Ω`, `(𝒢_u)_{u ≥ 0}` a filtration and `Y` a
[Markov family](is-neutral-markov-family.md) for the neutral Wright–Fisher semigroup with respect to
`(𝒢_u)` under `μ`. For all times `0 ≤ u ≤ v`, every `A ∈ 𝒢_u` and every measurable
`f : [0, 1] → [0, ∞]`, `∫_A f(Y_v) dμ = ∫_A ∫ f(y) K_{v - u}(Y_u, dy) dμ`, where `K` is the
[neutral Wright–Fisher kernel](../construction-of-the-neutral-wright-fisher-diffus/neutral-kernel.md).
