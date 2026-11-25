# Unique predecessor along a reaction among states containing its source

Let `N` be a [chemical reaction network](../../../Dynamics/smooth-dynamics/reaction-network.md) on
a set `S` of species, with reactions indexed by a set `ρ` (neither needs to be finite). Let `r` be
a reaction and `w, x ∈ ℕ^S` states with `src(r) ≤ w` componentwise. Then
[one firing](../../../Biology/systems-biology/stochastic-mass-action-metabolic-control-and-flu/fire.md)
of `r` from `w` leads to `x`, that is `w - src(r) + prod(r) = x`, if and only if `prod(r) ≤ x`
and `w = x - prod(r) + src(r)`, the
[state before one firing](../../../Biology/systems-biology/stochastic-mass-action-metabolic-control-and-flu/unfire.md)
of `r` at `x`. Under these conditions both natural-number subtractions are exact.

So among the states containing `src(r)`, the only states in which the propensity of `r` can be
nonzero, `x` has a predecessor along `r` only if `prod(r) ≤ x`, and then it is
`x - prod(r) + src(r)`. This is why the inflow side of the
[stationary chemical master equation](is-stationary-master-solution.md) at `x` has one term for
each reaction `r` with `prod(r) ≤ x`.
