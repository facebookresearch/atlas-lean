# A genuine bottleneck strictly shortens the oldest epoch on average

Let `T_k` (`k ∈ ℕ`) be
[Kingman holding times](../kingman-s-coalescent-and-watterson-s-estimator/kingman-times.md)
of a sample of size `n` under a measure `μ` on `Ω`: for `2 ≤ k ≤ n`, `T_k` has the exponential
law with rate `C(k, 2)` under `μ`, and `T_2, …, T_n` are independent.
Suppose `μ` is a probability measure, `n ≥ 2` and each `T_k` (`k ∈ ℕ`) is measurable, and let
`a ≥ 0`, `d > 0` and `0 < f < 1` be real numbers.
Then the [time-changed holding time](bottleneck-times.md) of the epoch with two
lineages satisfies

`∫ T^b_2 dμ < 1 = 1 / C(2, 2)`,

strictly below the mean Kingman holding time `E[T_2] = 1`.
