# Poisson mass of a set of states

Let `S` be a finite set, `c ∈ ℝ^S` and `Γ ⊆ ℕ^S` a set of states, possibly empty or infinite. The
mass of `Γ` under the product-form weights is `π_c(Γ) = ∑_{x ∈ Γ} π_c(x)`, where
`π_c(x) = ∏_s c_s^{x_s} e^{-c_s} / x_s!` is the
[Poisson weight](../../../Biology/systems-biology/stochastic-mass-action-metabolic-control-and-flu/poisson-weight.md)
of `x`. It is defined for every real `c`, and the series always converges absolutely:
`|π_c(x)| = (∏_s e^{|c_s| - c_s}) π_{|c|}(x)`, and the weights `π_{|c|}(x)`
[sum to one](../ergodic-theorem-for-complex-balanced-reaction-ne/has-sum-poisson-weight.md). So the
convention that a non-summable family sums to `0` never applies here, and `π_c(∅) = 0`.

For `c ≥ 0` the mass is the probability of `Γ` under the [product-form Poisson law](poisson-pmf.md),
a number in `[0, 1]`. It is [positive](class-mass-pos.md) when `c > 0` and `Γ` is nonempty. With
`c ≥ 0` alone a nonempty `Γ` can have mass `0`, since a state with `x_s ≥ 1` where `c_s = 0` has
weight `0`. If some `c_s < 0`, some weights are negative and a nonempty `Γ` can have mass `0` or
negative mass: for one species and `c = -1`, the set `{0, 1}` has mass `e - e = 0` and `{1}` has
mass `-e`.
