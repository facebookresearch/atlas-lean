# Ergodic theorem under a stationary law charging the regeneration state

Let `(Ω, P)` be a probability space, `σ` a measurable space in which singletons are measurable,
and `X : ℝ × Ω → σ` a jointly measurable process that [regenerates](is-regenerative.md) at a
state `x₀` at times `R_0 < R_1 < ⋯`. Let `ν` be a measure on `σ` such that `X_t` has law `ν` for
every `t ≥ 0`, with `ν({x₀}) > 0`. Then:

- `X` is [positive recurrent](is-positive-recurrent.md): `E[R_1 - R_0] < ∞`;
- for every measurable `f : σ → ℝ` with `|f| ≤ B` for some real `B`, almost surely the time
  averages of `f` ([occupation integrals](occupation.md) divided by `t`) converge to its mean
  under `ν`: `(1/t) ∫_0^t f(X_s) ds → ∫ f dν` as `t → ∞`.

The exceptional null set in the second conclusion may depend on `f`. "Ergodic" means these two
conclusions: positive recurrence and the almost sure convergence of the time averages of bounded
measurable observables to their means under `ν`. Only the one-time laws of `X` at nonnegative
times are assumed stationary. The proof combines
[positive recurrence from the stationary law](is-positive-recurrent-of-stationary.md), the
[renewal–reward theorem](ae-tendsto-occupation-div.md) and the
[identification of its limit](integral-div-eq-of-stationary.md).
