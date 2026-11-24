# Renewal–reward theorem for cycles of finite mean length

Let `(Ω, P)` be a probability space, `σ` a measurable space, `X : ℝ × Ω → σ` a jointly measurable
process, `f : σ → ℝ` a measurable function with `|f(x)| ≤ B` for every `x`, and
`R_0, R_1, … : Ω → ℝ` random times with `0 ≤ R_0(ω) < R_1(ω) < ⋯` for every `ω`. Suppose that the
[cycle lengths](cycle-length.md) `L_k = R_{k+1} - R_k` are pairwise independent and identically
distributed with `E[L_0] < ∞`, and that the [cycle rewards](cycle-reward.md)
`W_k = ∫_{R_k}^{R_{k+1}} f(X_s) ds` are pairwise independent and identically distributed. Then,
almost surely, the time averages of `f` (the [occupation integrals](occupation.md) divided by
`t`) converge:

`(1/t) ∫_0^t f(X_s) ds → E[W_0] / E[L_0]` as `t → ∞`.

Here `E[L_0] > 0` because `L_0 > 0`, and `W_0` is integrable because `|W_0| ≤ B L_0`. No
regeneration state is involved, and the lengths need not be independent of the rewards. The
proof applies the strong law of large numbers to the lengths and to the rewards, then the
[deterministic renewal–reward lemma](tendsto-div-of-renewal.md) along each path.
