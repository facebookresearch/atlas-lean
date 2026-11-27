# An expansion does not shorten any epoch on average

Let `T_k` (`k ∈ ℕ`) be
[Kingman holding times](../kingman-s-coalescent-and-watterson-s-estimator/kingman-times.md)
of a sample of size `n` under a measure `μ` on `Ω`: for `2 ≤ k ≤ n`, `T_k` has the exponential
law with rate `C(k, 2)` under `μ`, and `T_2, …, T_n` are independent.
Suppose each `T_k` (`k ∈ ℕ`) is measurable, let `a` be any real number, and let `d ≥ 0` and
`f ≥ 1`. For every `2 ≤ k ≤ n`, the [time-changed holding time](bottleneck-times.md) satisfies

`1 / C(k, 2) ≤ ∫ T^b_k dμ`,

where `1 / C(k, 2)` is the mean Kingman holding time (`μ` is a probability measure, since
`n ≥ 2`).
