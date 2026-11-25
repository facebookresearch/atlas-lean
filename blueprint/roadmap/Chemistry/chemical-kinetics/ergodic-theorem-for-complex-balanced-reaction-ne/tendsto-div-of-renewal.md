# Deterministic renewal–reward limit for a Lipschitz function

Let `F : ℝ → ℝ` satisfy `F(0) = 0` and `|F(t) - F(s)| ≤ B (t - s)` whenever `0 ≤ s ≤ t`, for a
real constant `B`: `F` is `B`-Lipschitz on `[0, ∞)`. Let `R : ℕ → ℝ` be strictly increasing with
`R_0 ≥ 0`, and suppose that `R_n / n → m` for some `m > 0` and `F(R_n) / n → w` as `n → ∞`. Then

`F(t) / t → w / m` as `t → ∞` through the reals.

This is the deterministic step of the [renewal–reward theorem](ae-tendsto-occupation-div.md), with
`F(t)` the occupation integral of a bounded observable up to time `t` and the `R_n` the
regeneration times.
