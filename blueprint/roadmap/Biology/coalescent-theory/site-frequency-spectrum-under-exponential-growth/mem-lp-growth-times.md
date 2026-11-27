# Each time-changed holding time is square integrable

Let `T_k` (`k ∈ ℕ`) be
[Kingman holding times](../kingman-s-coalescent-and-watterson-s-estimator/kingman-times.md) of a
sample of size `n` under a measure `μ` on `Ω`: for `2 ≤ k ≤ n`, `T_k` has the exponential law
with rate `C(k, 2)` under `μ`, and `T_2, …, T_n` are independent. Suppose each `T_k` (`k ∈ ℕ`)
is measurable, and let `ρ ≥ 0`. Then for every `2 ≤ k ≤ n` the
[time-changed holding time](growth-times.md) `T^ρ_k` is square integrable with respect to `μ`,
as `0 ≤ T^ρ_k ≤ T_k` almost everywhere and `T_k` is square integrable. Nothing more is assumed
of `μ`: since `n ≥ k ≥ 2`, the exponential law of `T_k` already makes `μ` a probability measure.
