# Stationary chemical master equation

Let `N` be a [chemical reaction network](../../../Dynamics/smooth-dynamics/reaction-network.md)
with finite species set `S` and finite reaction set `ρ`, let `κ ∈ ℝ^ρ`, and let
`λ_r(x) = κ_r ∏_s x_s (x_s - 1) ⋯ (x_s - src(r)_s + 1)` be the
[stochastic mass-action propensities](../../../Biology/systems-biology/stochastic-mass-action-metabolic-control-and-flu/propensity.md)
with rate constants `κ`. A function `p : ℕ^S → ℝ` solves the stationary chemical master equation
with rate constants `κ` when, at every state `x ∈ ℕ^S`,

`p(x) ∑_r λ_r(x) = ∑_{r : prod(r) ≤ x} p(x - prod(r) + src(r)) λ_r(x - prod(r) + src(r))`,

where the left sum runs over all reactions and the right one over the reactions `r` with
`prod(r) ≤ x` componentwise. The equation is defined for all real `κ` and every real function
`p`: no sign, summability or normalisation of `p` is required.

For `κ ≥ 0`, `λ_r(x)` is the rate at which reaction `r` fires in state `x` in the stochastic
mass-action chain. The left side is then the flow of `p` out of `x`, and the right side the flow
into `x`: by [uniqueness of predecessors](fire-eq-iff.md), `x - prod(r) + src(r)` is the only
state containing `src(r)` from which one firing of `r` leads to `x`. For a probability mass
function `p` (`p ≥ 0` and `∑_x p(x) = 1`) the equation says that `p` is a time-independent
solution of the chemical master equation, the stationary Kolmogorov forward equation `p Q = 0` of
the chain. Whether the chain started from such a `p` keeps the law `p` at all times is a separate
question, not settled by this equation; the [ergodic theorem](ergodic-of-is-complex-balanced.md)
takes it as a hypothesis, under non-explosion.
