# The most recent epoch lasts the time change of its Kingman duration

Let `T_k` (`k ∈ ℕ`) be
[Kingman holding times](../kingman-s-coalescent-and-watterson-s-estimator/kingman-times.md) of a
sample of size `n` under a measure `μ` on `Ω`: for `2 ≤ k ≤ n`, `T_k` has the exponential law
with rate `C(k, 2)` under `μ`, and `T_2, …, T_n` are independent. Let `ρ` be a real number.
For every `ω ∈ Ω`, the [time-changed holding time](growth-times.md) of the most recent epoch,
with `n` lineages, is

`T^ρ_n(ω) = G(T_n(ω))`,

where `G` is the [time change](growth-time.md) for exponential growth at rate `ρ`.
