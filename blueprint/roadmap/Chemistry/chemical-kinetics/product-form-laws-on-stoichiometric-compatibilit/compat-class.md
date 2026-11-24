# Stoichiometric compatibility class of a state

Let `N` be a [chemical reaction network](../../../Dynamics/smooth-dynamics/reaction-network.md) with
species set `S` and reaction set `ρ`, and let `𝒮 ⊆ ℝ^S` be its
[stoichiometric subspace](../../../Dynamics/smooth-dynamics/stoichiometric-subspace.md), the span of
the reaction vectors `prod(r) - src(r)`. The stoichiometric compatibility class of a state
`x₀ ∈ ℕ^S` is the set of states `x ∈ ℕ^S` with `x - x₀ ∈ 𝒮`, the difference taken in `ℝ^S`. Neither
`S` nor `ρ` needs to be finite.

The class contains `x₀`, so it is never empty, and it can be finite or infinite: for the single
reaction `0 → A` it is all of `ℕ`, and for `A ⇌ B` it is the finite set of states with
`x_A + x_B = (x₀)_A + (x₀)_B`. It is [reaction-closed](is-reaction-closed-compat-class.md), so it
contains every state reached from `x₀` by firing reactions, and it can contain more: for `2A ⇌ 0` it
is all of `ℕ`, while every firing changes `x_A` by `±2` and so keeps its parity.
