# Kernel form of the Markov property

Let `κ = (κ_t)_{t ≥ 0}` be a family of Markov kernels on `[0, 1]`, `μ` a finite measure on a
measurable space `Ω`, `(𝒢_u)_{u ≥ 0}` a filtration and `Y` a
[Markov family for `κ`](is-kernel-markov-family.md) with respect to `(𝒢_u)` under `μ`. For all times
`0 ≤ u ≤ v` and every `A ∈ 𝒢_u`, the law of `Y_v` under `μ` restricted to `A` is
`∫ κ_{v - u}(y, ·) ν(dy)`, where `ν` is the law of `Y_u` under `μ` restricted to `A`.
