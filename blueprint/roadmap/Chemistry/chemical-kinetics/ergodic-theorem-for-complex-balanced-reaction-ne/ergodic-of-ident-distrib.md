# Ergodic limits transfer to a process with the same cycle laws

Let `(Ω, P)` be a probability space, `σ` a measurable space in which singletons are measurable,
and `X : ℝ × Ω → σ` a jointly measurable process that [regenerates](is-regenerative.md) at a
state `x₀` at times `R_0 < R_1 < ⋯`, such that `X_t` has law `ν` for every `t ≥ 0`, where `ν` is
a measure on `σ` with `ν({x₀}) > 0`. Let `(Ω', P')` be another probability space and
`X' : ℝ × Ω' → σ` a jointly measurable process that regenerates under `P'` at some state `x₀'`,
possibly different from `x₀`, at times `R'_0 < R'_1 < ⋯`, such that

- its first [cycle length](cycle-length.md) `R'_1 - R'_0` has the law of `R_1 - R_0`;
- for every measurable `g : σ → ℝ` bounded by some real constant, its first
  [cycle reward](cycle-reward.md) `∫_{R'_0}^{R'_1} g(X'_s) ds` has the law of
  `∫_{R_0}^{R_1} g(X_s) ds`.

Then for every measurable `f : σ → ℝ` with `|f| ≤ B`, `P'`-almost surely

`(1/t) ∫_0^t f(X'_s) ds → ∫ f dν` as `t → ∞`,

the limit of the [ergodic theorem](ergodic.md) for `X`. No stationarity is assumed for `X'`. For
instance, if `X` is a Markov chain started from `ν` and both processes regenerate at their
successive entrance times into `x₀`, `X'` can be the same chain started from a fixed state: by
the strong Markov property, the cycles of both are distributed as those of the chain started at
`x₀`.
