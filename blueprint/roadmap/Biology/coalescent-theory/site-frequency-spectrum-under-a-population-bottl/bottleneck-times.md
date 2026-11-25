# Kingman holding times after the bottleneck time change

Let `T_k` (`k ∈ ℕ`) be
[Kingman holding times](../kingman-s-coalescent-and-watterson-s-estimator/kingman-times.md)
of a sample of size `n` under a measure `μ` on `Ω`: for `2 ≤ k ≤ n`, `T_k` has the exponential
law with rate `C(k, 2)` under `μ`, and `T_2, …, T_n` are independent.
Let `a`, `d` and `f` be real numbers. For every natural number `k` and every `ω ∈ Ω`, let

`T^b_k(ω) = G(V_k(ω)) - G(V_{k+1}(ω))`,

the [time-changed holding time](bottleneck-holding.md) of the sequence `(T_j(ω))_{j ∈ ℕ}`, with
`V_k = ∑_{j=k}^{n} T_j` (`0` for `k > n`) and the [time change](bottleneck-time.md) `G`; so
`T^b_k = 0` for `k > n`. With `a ≥ 0`, `d ≥ 0` and `f > 0`, `T^b_k` (`2 ≤ k ≤ n`) is the real
duration of the epoch with `k` lineages in the genealogy of a sample from a population with the
[bottleneck history](bottleneck-size.md).
