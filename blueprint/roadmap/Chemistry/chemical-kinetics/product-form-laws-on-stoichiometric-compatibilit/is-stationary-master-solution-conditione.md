# Complex balance makes the law on a reaction-closed set stationary

Let `N` be a [chemical reaction network](../../../Dynamics/smooth-dynamics/reaction-network.md) with
finite species set `S` and finite reaction set `ρ`, let `κ ∈ ℝ^ρ` be rate constants and let
`c ∈ ℝ^S` be
[complex balanced](../../../Biology/systems-biology/complex-balancing-and-the-deficiency-zero-theore/is-complex-balanced.md)
for `κ`. For every [reaction-closed](is-reaction-closed.md) set `Γ ⊆ ℕ^S`, the
[conditioned law](conditioned-law.md) `π_c(· | Γ)` solves the
[stationary master equation](../ergodic-theorem-for-complex-balanced-reaction-ne/is-stationary-master-solution.md)
for `κ` at every state of `ℕ^S`. The Poisson weights `π_c` solve it by the
[Anderson–Craciun–Kurtz theorem](../../../Biology/systems-biology/stochastic-mass-action-metabolic-control-and-flu/poisson-weight-mul-sum-propensity.md),
and [restricting](is-stationary-master-solution-indicator.md) them to `Γ` and
[dividing](is-stationary-master-solution-div-const.md) by the constant `π_c(Γ)` keeps a solution.

No sign condition is assumed: the statement holds for all real `κ` and `c`. When `π_c(Γ) = 0`, for
example for `Γ = ∅`, the conditioned law is `0` by the convention `y / 0 = 0`, and the statement is
trivial. In the stochastic model `κ ≥ 0`, which makes the equation the master equation of a chain,
and `c` is positive; then, for nonempty `Γ`, the conditioned law is a probability solution, which
need not be the only one.
