# Kernel form of the Markov property

Let `μ` be a finite measure on a measurable space `Ω`, `(𝒢_u)_{u ≥ 0}` a filtration and `Y` a
[Markov family](is-neutral-markov-family.md) for the neutral Wright–Fisher semigroup with respect to
`(𝒢_u)` under `μ`. For all times `0 ≤ u ≤ v` and every `A ∈ 𝒢_u`, the law of `Y_v` under `μ`
restricted to `A` is `∫ K_{v - u}(y, ·) ν(dy)`, where `ν` is the law of `Y_u` under `μ` restricted
to `A` and `K` is the
[neutral Wright–Fisher kernel](../construction-of-the-neutral-wright-fisher-diffus/neutral-kernel.md).
