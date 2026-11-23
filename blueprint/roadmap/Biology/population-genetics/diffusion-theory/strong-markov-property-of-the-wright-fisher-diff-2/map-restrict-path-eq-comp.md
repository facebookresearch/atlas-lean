# Path law of a Markov family

Let `κ = (κ_t)_{t ≥ 0}` be a family of Markov kernels on `[0, 1]`, `μ` a finite measure on a
measurable space `Ω`, `(𝒢_u)_{u ≥ 0}` a filtration and `Y` a
[Markov family for `κ`](is-kernel-markov-family.md) with respect to `(𝒢_u)` under `μ`. Suppose
moreover that `κ` satisfies the Chapman–Kolmogorov equations
`κ_{s + t}(x, ·) = ∫ κ_t(y, ·) κ_s(x, dy)`. Then for every `A ∈ 𝒢_0`, the law of the path
`(Y_u)_{u ≥ 0}` under `μ` restricted to `A` is `∫ P^κ_y ν(dy)`, where `ν` is the law of `Y_0` under
`μ` restricted to `A` and `P^κ_y` is the
[path measure](../../../../Probability/markov-chains/markov-processes-from-transition-semigroups/path-measure.md)
of `κ` from `y`.
