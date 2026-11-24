# Complex-balanced Poisson weights solve the stationary master equation

Let `N` be a [chemical reaction network](../../../Dynamics/smooth-dynamics/reaction-network.md)
with finite species set `S` and finite reaction set `ρ`, let `κ ∈ ℝ^ρ`, and let `c ∈ ℝ^S` be
[complex balanced](../../../Biology/systems-biology/complex-balancing-and-the-deficiency-zero-theore/is-complex-balanced.md)
for `κ`. Then the
[product-form Poisson weights](../../../Biology/systems-biology/stochastic-mass-action-metabolic-control-and-flu/poisson-weight.md)
`π_c(x) = ∏_s c_s^{x_s} e^{-c_s} / x_s!` (natural powers, with `0^0 = 1`) solve the
[stationary chemical master equation](is-stationary-master-solution.md) with rate constants `κ`
at every state `x ∈ ℕ^S`:

`π_c(x) ∑_r λ_r(x) = ∑_{r : prod(r) ≤ x} π_c(x - prod(r) + src(r)) λ_r(x - prod(r) + src(r))`,

where the `λ_r` are the
[stochastic mass-action propensities](../../../Biology/systems-biology/stochastic-mass-action-metabolic-control-and-flu/propensity.md)
with rate constants `κ` (Anderson, Craciun & Kurtz 2010, Theorem 4.1).

This is an algebraic identity: `κ` and `c` may be any real vectors, with no sign condition, and
`π_c` is a weight function that need not be nonnegative or normalised. For `c ≥ 0` the weights are
nonnegative and [sum to `1` over `ℕ^S`](has-sum-poisson-weight.md), so for `κ ≥ 0` and `c ≥ 0` the
function `π_c` is a probability mass function solving the stationary master equation of the
stochastic mass-action chain. That the chain started from `π_c` keeps this law at all times does
not follow from the identity alone; the [ergodic theorem](ergodic-of-is-complex-balanced.md) takes
it as a hypothesis, under non-explosion.
