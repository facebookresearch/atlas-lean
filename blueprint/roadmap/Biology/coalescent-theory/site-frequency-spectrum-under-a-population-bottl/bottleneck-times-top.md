# Bottleneck holding time at index n is the time change of T_n

Let `T_k` (`k ∈ ℕ`) be
[Kingman holding times](../kingman-s-coalescent-and-watterson-s-estimator/kingman-times.md)
of a sample of size `n` under a measure `μ` on `Ω`: for `2 ≤ k ≤ n`, `T_k` has the exponential
law with rate `C(k, 2)` under `μ`, and `T_2, …, T_n` are independent.
Let `a ≥ 0`, `d ≥ 0` and `f > 0` be real numbers. For every `ω ∈ Ω`, the
[time-changed holding time](bottleneck-times.md) with index `n` is

`T^b_n(ω) = G(T_n(ω))`,

with the [time change](bottleneck-time.md) `G`. This identity holds for every natural number
`n`, including `n < 2`, where there is no coalescence epoch and no law is imposed on `T_n`. For
`n ≥ 2`, `T_n` is the standard duration of the most recent epoch, with `n` lineages, and is
positive `μ`-almost surely; that epoch then lasts `G(T_n)` in real time.
