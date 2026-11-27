# Mean occupation integral under a stationary law

Let `(Ω, P)` be a probability space, `X : ℝ × Ω → σ` a jointly measurable process, `f : σ → ℝ` a
measurable function with `|f(x)| ≤ B` for every `x`, and `ν` a measure on `σ` such that `X_t` has
law `ν` for every `t ≥ 0`. Then for every `t ≥ 0` the [occupation integral](occupation.md) has
mean

`E[∫_0^t f(X_s) ds] = t ∫ f dν`.

Only the one-time laws of `X` at nonnegative times are constrained, and `ν`, the law of `X_0`, is
a probability measure. The proof exchanges the two integrals by Fubini's theorem. For `t < 0` the
identity can fail, as nothing constrains `X` at negative times.
