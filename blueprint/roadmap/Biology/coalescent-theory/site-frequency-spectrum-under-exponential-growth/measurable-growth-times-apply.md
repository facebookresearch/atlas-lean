# Each time-changed holding time is measurable

Let `T_k` (`k ∈ ℕ`) be
[Kingman holding times](../kingman-s-coalescent-and-watterson-s-estimator/kingman-times.md) of a
sample of size `n` under a measure `μ` on `Ω`: for `2 ≤ k ≤ n`, `T_k` has the exponential law
with rate `C(k, 2)` under `μ`, and `T_2, …, T_n` are independent. Suppose each `T_k` (`k ∈ ℕ`)
is measurable, and let `ρ` be a real number. Then the map `ω ↦ (T^ρ_k(ω))_{k ∈ ℕ}` from `Ω` to
the sequence space `ℝ^ℕ`, with its product σ-algebra, is measurable, where `T^ρ_k` are the
[time-changed holding times](growth-times.md). Equivalently, since a map into `ℝ^ℕ` is measurable
for the product σ-algebra exactly when every coordinate is, for every natural number `k` the
time-changed holding time `T^ρ_k` is a measurable function on `Ω`.
