# Restricting a master-equation solution to a reaction-closed set

Let `N` be a [chemical reaction network](../../../Dynamics/smooth-dynamics/reaction-network.md) with
finite species set `S` and finite reaction set `ρ`, and let `κ ∈ ℝ^ρ` be rate constants of any sign.
If a function `p : ℕ^S → ℝ` solves the
[stationary master equation](../ergodic-theorem-for-complex-balanced-reaction-ne/is-stationary-master-solution.md)
for `κ` at every state, and `Γ ⊆ ℕ^S` is [reaction-closed](is-reaction-closed.md), then the function
equal to `p` on `Γ` and to `0` off `Γ` also solves it at every state. At a state `x ∈ Γ`, every
predecessor `x - prod(r) + src(r)` with `prod(r) ≤ x` lies in `Γ`; at a state `x ∉ Γ` none does,
since firing `r` from a predecessor in `Γ` would lead to `x` inside `Γ`.
