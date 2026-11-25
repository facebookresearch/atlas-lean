# Product-form limits for a process with the stationary cycle laws

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

Let `(Ω', P')` be another probability space and `X' : ℝ × Ω' → ℕ^S` a jointly measurable process
that regenerates under `P'` at some state `x₀'`, possibly different from `x₀`, at times
`R'_0 < R'_1 < ⋯`, such that its first [cycle length](cycle-length.md) `R'_1 - R'_0` has the law
of `R_1 - R_0` and, for every bounded `g : ℕ^S → ℝ`, its first [cycle reward](cycle-reward.md)
`∫_{R'_0}^{R'_1} g(X'_s) ds` has the law of `∫_{R_0}^{R_1} g(X_s) ds`. Then for every
`f : ℕ^S → ℝ` with `|f(x)| ≤ B` for every `x`, `P'`-almost surely

`(1/t) ∫_0^t f(X'_s) ds → ∑_{x ∈ ℕ^S} π_c(x) f(x)` as `t → ∞`,

the limit of the [ergodic theorem for complex-balanced networks](ergodic-of-is-complex-balanced.md)
for `X`. No stationarity is assumed for `X'`. For instance, `X` can be the stochastic mass-action
chain started from `π_c` and `X'` the same chain started from a fixed state, both regenerating at
their successive entrance times into `x₀`: by the strong Markov property, their cycles are
distributed as those of the chain started at `x₀`. The nonnegativity of `κ` is not needed for the
conclusion.
