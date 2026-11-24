# Under growth each mean holding time is at most its Kingman value

Let `T_k` (`k ∈ ℕ`) be
[Kingman holding times](../kingman-s-coalescent-and-watterson-s-estimator/kingman-times.md) of a
sample of size `n` under a measure `μ` on `Ω`: for `2 ≤ k ≤ n`, `T_k` has the exponential law
with rate `C(k, 2)` under `μ`, and `T_2, …, T_n` are independent. Suppose each `T_k` (`k ∈ ℕ`)
is measurable, and let `ρ ≥ 0`. Then for every `2 ≤ k ≤ n` the
[time-changed holding time](growth-times.md) `T^ρ_k` satisfies

`E[T^ρ_k] ≤ 1 / C(k, 2)`,

the [mean Kingman holding time](../kingman-s-coalescent-and-watterson-s-estimator/integral-t.md) `E[T_k]`. Here `E` is the
integral against `μ`, a probability measure since `n ≥ k ≥ 2`. Growth never lengthens an epoch
on average.
