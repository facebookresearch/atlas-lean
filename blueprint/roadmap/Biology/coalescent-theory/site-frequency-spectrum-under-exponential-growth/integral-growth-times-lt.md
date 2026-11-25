# Under strict growth each mean holding time is below its Kingman value

Let `μ` be a probability measure on `Ω` and let `T_k` (`k ∈ ℕ`) be
[Kingman holding times](../kingman-s-coalescent-and-watterson-s-estimator/kingman-times.md) of a
sample of size `n` under `μ`, each `T_k` measurable: for `2 ≤ k ≤ n`, `T_k` has the exponential
law with rate `C(k, 2)`, and `T_2, …, T_n` are independent. Let `ρ > 0`. Then for every
`2 ≤ k ≤ n` the [time-changed holding time](growth-times.md) `T^ρ_k` satisfies

`E[T^ρ_k] < 1 / C(k, 2)`,

the [mean Kingman holding time](../kingman-s-coalescent-and-watterson-s-estimator/integral-t.md) `E[T_k]`.
