# Almost-sure bounds on the time-changed epochs

Let `T_k` (`k ∈ ℕ`) be
[Kingman holding times](../kingman-s-coalescent-and-watterson-s-estimator/kingman-times.md)
of a sample of size `n` under a measure `μ` on `Ω`: for `2 ≤ k ≤ n`, `T_k` has the exponential
law with rate `C(k, 2)` under `μ`, and `T_2, …, T_n` are independent.
Let `a` be any real number, and let `d ≥ 0` and `f > 0`. For `μ`-almost every `ω`, every
`2 ≤ k ≤ n` satisfies `0 ≤ T^b_k(ω) ≤ max(1, f) T_k(ω)`, with `T^b_k(ω) ≤ T_k(ω)` if `f ≤ 1` and
`T_k(ω) ≤ T^b_k(ω)` if `f ≥ 1`, where `T^b_k` are the
[time-changed holding times](bottleneck-times.md): the
[pointwise bounds](bottleneck-holding-bounds.md) apply because Kingman holding times are almost
surely positive.
