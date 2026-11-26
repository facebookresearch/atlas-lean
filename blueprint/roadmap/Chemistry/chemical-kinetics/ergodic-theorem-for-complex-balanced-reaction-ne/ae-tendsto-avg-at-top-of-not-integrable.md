# Strong law of large numbers for nonnegative variables of infinite mean

Let `(Ω, P)` be a probability space and `L_0, L_1, … : Ω → ℝ` random variables with
`L_k(ω) ≥ 0` for every `k` and `ω`, pairwise independent, each with the law of `L_0`, and with
`L_0` not integrable. Then almost surely

`(1/n) ∑_{k<n} L_k → ∞` as `n → ∞`.

Having the law of `L_0` includes measurability up to null sets, so for these nonnegative
variables non-integrability means `E[L_0] = ∞`. The proof applies the strong law of large numbers
to the truncations `min(L_k, M)` and lets `M → ∞` by monotone convergence.
