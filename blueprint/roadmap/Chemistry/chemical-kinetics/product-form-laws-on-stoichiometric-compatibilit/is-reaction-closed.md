# Reaction-closed set of states

Let `N` be a [chemical reaction network](../../../Dynamics/smooth-dynamics/reaction-network.md) with
species set `S` and reaction set `ρ`. A set `Γ ⊆ ℕ^S` of states is reaction-closed when, for every
`x ∈ Γ` and every reaction `r`, the
[state after one firing](../../../Biology/systems-biology/stochastic-mass-action-metabolic-control-and-flu/fire.md)
`x - src(r) + prod(r)` lies in `Γ` whenever `src(r) ≤ x`, and the
[state before one firing](../../../Biology/systems-biology/stochastic-mass-action-metabolic-control-and-flu/unfire.md)
`x - prod(r) + src(r)` lies in `Γ` whenever `prod(r) ≤ x`. The inequalities are coordinatewise, and
under them both subtractions are exact.

So firing a reaction from a state of `Γ` stays in `Γ`, and so does the
[unique state](../ergodic-theorem-for-complex-balanced-reaction-ne/fire-eq-iff.md) from which one
firing of `r` leads to a state `x` of `Γ`, which exists exactly when `prod(r) ≤ x`. The empty set
and `ℕ^S` are reaction-closed, and so is every
[compatibility class](is-reaction-closed-compat-class.md).
