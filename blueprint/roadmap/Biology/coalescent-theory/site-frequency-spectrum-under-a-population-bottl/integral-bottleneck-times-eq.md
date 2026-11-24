# Without a size change every epoch keeps its Kingman mean

Let `T_k` (`k ∈ ℕ`) be
[Kingman holding times](../kingman-s-coalescent-and-watterson-s-estimator/kingman-times.md)
of a sample of size `n` under a measure `μ` on `Ω`: for `2 ≤ k ≤ n`, `T_k` has the exponential
law with rate `C(k, 2)` under `μ`, and `T_2, …, T_n` are independent.
Let `a`, `d` and `f` be real numbers with `f = 1` or `d = 0`. For every `2 ≤ k ≤ n`, the
[time-changed holding time](bottleneck-times.md) satisfies `∫ T^b_k dμ = 1 / C(k, 2)`, the mean
Kingman holding time (`μ` is a probability measure, since `n ≥ 2`).
