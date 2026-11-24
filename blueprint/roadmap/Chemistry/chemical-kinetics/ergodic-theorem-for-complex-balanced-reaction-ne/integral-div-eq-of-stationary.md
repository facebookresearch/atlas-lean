# Under a stationary law, the renewal–reward limit is the space average

Let `(Ω, P)` be a probability space, `X : ℝ × Ω → σ` a jointly measurable process, `f : σ → ℝ` a
measurable function with `|f(x)| ≤ B` for every `x`, and `R_0, R_1, … : Ω → ℝ` random times with
`0 ≤ R_0(ω) < R_1(ω) < ⋯` for every `ω`. Suppose that the [cycle lengths](cycle-length.md)
`L_k = R_{k+1} - R_k` are pairwise independent and identically distributed with `E[L_0] < ∞`, and
that the [cycle rewards](cycle-reward.md) `W_k = ∫_{R_k}^{R_{k+1}} f(X_s) ds` are pairwise
independent and identically distributed. If `ν` is a measure on `σ` such that `X_t` has law `ν`
for every `t ≥ 0`, then the limit of the [renewal–reward theorem](ae-tendsto-occupation-div.md)
is the space average of `f`:

`E[W_0] / E[L_0] = ∫ f dν`.

The proof takes means in the almost sure limit of the time averages at integer times, by bounded
convergence, and uses the [mean occupation integral](integral-occupation.md)
`E[∫_0^n f(X_s) ds] = n ∫ f dν`.
