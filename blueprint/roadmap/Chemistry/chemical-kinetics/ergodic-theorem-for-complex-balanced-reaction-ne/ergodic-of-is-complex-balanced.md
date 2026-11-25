# Ergodic theorem for complex-balanced networks under regeneration

Let `N` be a [chemical reaction network](../../../Dynamics/smooth-dynamics/reaction-network.md)
with finite species set `S` and finite reaction set `ρ`, let `κ ∈ ℝ^ρ` with `κ_r ≥ 0` for every
`r`, and let `c ∈ ℝ^S`, with `c_s > 0` for every `s`, be
[complex balanced](../../../Biology/systems-biology/complex-balancing-and-the-deficiency-zero-theore/is-complex-balanced.md)
for `κ`. Write `π_c` for the
[product-form Poisson weights](../../../Biology/systems-biology/stochastic-mass-action-metabolic-control-and-flu/poisson-weight.md)
and `μ_p` for the [measure with mass function](count-law.md) `p`. Let `(Ω, P)` be a probability
space and `X : ℝ × Ω → ℕ^S` a jointly measurable process such that:

- `X` [does not explode](no-explosion.md);
- if `X` does not explode, then for every `p : ℕ^S → ℝ` with `p ≥ 0` and `∑_x p(x) = 1` that
  solves the [stationary chemical master equation](is-stationary-master-solution.md) with rate
  constants `κ`: if `X_0` has law `μ_p`, then `X_t` has law `μ_p` for every `t ≥ 0`;
- `X_0` has law `μ_{π_c}`;
- `X` [regenerates](is-regenerative.md) at a state `x₀ ∈ ℕ^S` at times `R_0 < R_1 < ⋯`.

Then `X` is [positive recurrent](is-positive-recurrent.md), `E[R_1 - R_0] < ∞`, and for every
`f : ℕ^S → ℝ` with `|f(x)| ≤ B` for every `x`, almost surely

`(1/t) ∫_0^t f(X_s) ds → ∑_{x ∈ ℕ^S} π_c(x) f(x)` as `t → ∞`,

an absolutely convergent series; the exceptional null set may depend on `f`. "Ergodic" means
these two conclusions. The statement concerns bounded observables only, and says nothing about
the convergence of `P(X_t = x)`.

By the [Anderson–Craciun–Kurtz theorem](../../../Biology/systems-biology/stochastic-mass-action-metabolic-control-and-flu/poisson-weight-mul-sum-propensity.md) and
[normalisation](has-sum-poisson-weight.md), `π_c` is a probability mass function solving the
stationary master equation, and `π_c(x₀) > 0` because `c > 0`. Given the first and third
hypotheses, the second holds if and only if `X_t` has law `μ_{π_c}` for every `t ≥ 0`: it is used
only for `p = π_c`, and non-explosion serves only as its premise. The
[ergodic theorem for a regenerative process](ergodic.md) with this stationary law then gives the
conclusion, the space average being the [weighted sum](integral-count-law.md) above. The
nonnegativity of `κ` is not needed for the conclusion; it makes the propensities nonnegative, as
jump rates must be.

In the intended application `X` is the stochastic mass-action chain of `N`: the continuous-time
Markov chain on `ℕ^S` that jumps from `x` to `x - src(r) + prod(r)` at rate `λ_r(x)`, the
[propensity](../../../Biology/systems-biology/stochastic-mass-action-metabolic-control-and-flu/propensity.md)
of `r`, with initial state independent of its jump mechanism. For that chain the second hypothesis
is the forward-equation step from `π Q = 0` to `π P(t) = π` (Norris 1997, Theorem 3.5.5), which can
fail for explosive chains; and when the chain enters `x₀` almost surely, with `x₀` recurrent and not
absorbing, the strong Markov property gives the regeneration at the successive entrance times into
`x₀`, once a null set of paths is discarded. The theorem does not assume that `X` is this chain: the
process is tied to the network only through the second hypothesis.

No irreducibility is assumed; it is implicit in the regeneration hypothesis, which asks every
path to visit `x₀`. For the chain started from `π_c`, which charges every state of `ℕ^S`, this
requires `x₀` to be reachable from every state. It fails, for example, when the network has a
conservation law, a nonzero vector `m` orthogonal to every reaction vector `prod(r) - src(r)`:
the chain never leaves the level set of `x ↦ m · x` containing its initial state.

For the chain built by the jump–hold construction, the same almost sure limits hold from every
initial state under a Foster–Lyapunov drift bound, `L V ≤ a V + b` for the generator `L` of the
mass-action chain, with `a, b ≥ 0` and some `V : ℕ^S → [0, ∞)` with `∑_s x_s ≤ V(x)` for every
`x`, and the reachability of every state from `x₀` along reactions of positive propensity, with
no hypothesis of non-explosion, stationarity or regeneration ([ergodic theorem under a drift bound and reachability](../regeneration-of-stochastic-reaction-networks/ergodic-of-is-complex-balanced-of-reacha.md)).
