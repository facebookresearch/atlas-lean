# Without growth each mean holding time is the Kingman value

Let `T_k` (`k ∈ ℕ`) be
[Kingman holding times](../kingman-s-coalescent-and-watterson-s-estimator/kingman-times.md) of a
sample of size `n` under a measure `μ` on `Ω`: for `2 ≤ k ≤ n`, `T_k` has the exponential law
with rate `C(k, 2)` under `μ`, and `T_2, …, T_n` are independent. Then for every `2 ≤ k ≤ n`
the [time-changed holding time](growth-times.md) at rate `ρ = 0`, which is `T^0_k = T_k`, has
mean

`E[T^0_k] = 1 / C(k, 2)`.

Here `E` is the integral against `μ`, a probability measure since `n ≥ k ≥ 2`.
