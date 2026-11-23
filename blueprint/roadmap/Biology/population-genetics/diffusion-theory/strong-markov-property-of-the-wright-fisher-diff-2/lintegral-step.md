# Kernel form of the Markov property for nonnegative functions

Let `κ = (κ_t)_{t ≥ 0}` be a family of Markov kernels on `[0, 1]`, `μ` a finite measure on a
measurable space `Ω`, `(𝒢_u)_{u ≥ 0}` a filtration and `Y` a
[Markov family for `κ`](is-kernel-markov-family.md) with respect to `(𝒢_u)` under `μ`. For all times
`0 ≤ u ≤ v`, every `A ∈ 𝒢_u` and every measurable `f : [0, 1] → [0, ∞]`,
`∫_A f(Y_v) dμ = ∫_A ∫ f(y) κ_{v - u}(Y_u, dy) dμ`.
