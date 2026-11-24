# The equilibrium equations decouple across independent linkage classes

Let `N` be a [chemical reaction network](../../../Dynamics/smooth-dynamics/reaction-network.md) with
finite species set `S` and finite reaction set `ρ`, and suppose that the
[stoichiometric subspaces `𝒮_θ` of its linkage classes](linkage-class-stoichiometric-subspace.md)
are independent: each `𝒮_θ` meets the sum of the others only in `0`. Then for all real rate
constants `k ∈ ℝ^ρ` and all `x ∈ ℝ^S`,

`f(x) = 0` if and only if `f_θ(x) = 0` for every linkage class `θ`,

where `f` is the [mass-action vector field](../../../Dynamics/smooth-dynamics/mass-action-field.md)
and `f_θ` the [mass-action field of `θ`](linkage-class-field.md), both with rate constants `k`. In
the model the rate constants are positive and the concentrations nonnegative; the equivalence holds
for all real `k` and `x`.
