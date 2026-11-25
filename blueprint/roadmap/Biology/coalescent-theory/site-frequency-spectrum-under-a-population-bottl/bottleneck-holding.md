# Holding times after the bottleneck time change

For real numbers `a`, `d` and `f`, a natural number `n` and real numbers `T_j` (`j ∈ ℕ`), let
[`V_k = ∑_{j=k}^{n} T_j`](../site-frequency-spectrum-under-exponential-growth/epoch-end.md)
(an empty sum, `0`, for `k > n`) and, for every natural number `k`,

`T^b_k = G(V_k) - G(V_{k+1})`,

with the [time change](bottleneck-time.md) `G`; in particular `T^b_k = 0` for `k > n`. When
`a ≥ 0`, `d ≥ 0`, `f > 0` and `T_2, …, T_n` are standard-coalescent holding times, the epoch
with `k` lineages (`2 ≤ k ≤ n`), which lasts from `V_{k+1}` to `V_k` in standard time, lasts
`T^b_k` in real time.
