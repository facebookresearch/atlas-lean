# A bottleneck does not lengthen any epoch on average

Let `T_k` (`k ∈ ℕ`) be
[Kingman holding times](../kingman-s-coalescent-and-watterson-s-estimator/kingman-times.md)
of a sample of size `n` under a measure `μ` on `Ω`: for `2 ≤ k ≤ n`, `T_k` has the exponential
law with rate `C(k, 2)` under `μ`, and `T_2, …, T_n` are independent.
Suppose each `T_k` (`k ∈ ℕ`) is measurable, let `a` be any real number, and let `d ≥ 0` and
`0 < f ≤ 1`. For every `2 ≤ k ≤ n`, the [time-changed holding time](bottleneck-times.md) satisfies

`∫ T^b_k dμ ≤ 1 / C(k, 2)`,

the mean Kingman holding time (`μ` is a probability measure, since `n ≥ 2`).
