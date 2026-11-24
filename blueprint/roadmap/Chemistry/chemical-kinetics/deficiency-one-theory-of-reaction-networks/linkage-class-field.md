# Mass-action field of a linkage class

Let `N` be a [chemical reaction network](../../../Dynamics/smooth-dynamics/reaction-network.md) with
finite species set `S` and finite reaction set `ρ`, let `θ` be a linkage class of `N`, and let
`k ∈ ℝ^ρ` be rate constants. The mass-action field of `θ` is the map `f_θ : ℝ^S → ℝ^S`,

`f_θ(x) = ∑_{r ∈ ρ_θ} k_r (∏_{s ∈ S} x_s ^ src(r)_s) (prod(r) - src(r))`,

where `ρ_θ` is the set of [reactions of `θ`](linkage-class-of.md): the part of the
[mass-action vector field](../../../Dynamics/smooth-dynamics/mass-action-field.md) contributed by
those reactions. The exponents are natural numbers, so `x_s ^ 0 = 1` also when `x_s = 0`. The
definition allows all real `k` and `x`; in the model the rate constants are positive and the
concentrations `x` nonnegative.
