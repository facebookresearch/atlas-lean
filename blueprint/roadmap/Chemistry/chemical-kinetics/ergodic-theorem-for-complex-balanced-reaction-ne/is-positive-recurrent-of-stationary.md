# Positive recurrence if a stationary law charges the regeneration state

Let `(Ω, P)` be a probability space, `σ` a measurable space in which singletons are measurable,
and `X : ℝ × Ω → σ` a jointly measurable process that [regenerates](is-regenerative.md) at a
state `x₀` at times `R_0 < R_1 < ⋯`. If `ν` is a measure on `σ` such that `X_t` has law `ν` for
every `t ≥ 0`, and `ν({x₀}) > 0`, then `X` is [positive recurrent](is-positive-recurrent.md): the
first cycle length is integrable, `E[R_1 - R_0] < ∞`.

Otherwise the [strong law for infinite mean](ae-tendsto-avg-at-top-of-not-integrable.md) gives
`R_n / n → ∞` almost surely, and the
[deterministic renewal lemma](tendsto-div-zero-of-renewal.md) makes the long-run fraction of time
spent in `x₀` vanish almost surely. By bounded convergence its mean vanishes too, but under `ν`
the mean fraction of time spent in `x₀` up to any time `t > 0` is `ν({x₀}) > 0`.
