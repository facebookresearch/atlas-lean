# Growth holding time at index n is the time change of T_n

Let `T_k` (`k ∈ ℕ`) be
[Kingman holding times](../kingman-s-coalescent-and-watterson-s-estimator/kingman-times.md) of a
sample of size `n` under a measure `μ` on `Ω`: for `2 ≤ k ≤ n`, `T_k` has the exponential law
with rate `C(k, 2)` under `μ`, and `T_2, …, T_n` are independent. Let `ρ` be a real number.
For every `ω ∈ Ω`, the [time-changed holding time](growth-times.md) with index `n` is

`T^ρ_n(ω) = G(T_n(ω))`,

where `G` is the [time change](growth-time.md) for exponential growth at rate `ρ`. The identity
holds for every natural number `n`, every real `ρ` and every value of `T_n(ω)`; for `n = 0` or
`n = 1` there is no epoch with `n` lineages and `T_n` is unconstrained. For `n ≥ 2`, `T_n` is the
holding time of the most recent epoch, with `n` lineages, and when `ρ ≥ 0` and `T_n(ω) ≥ 0`
(which holds for `μ`-almost every `ω`), `G(T_n(ω))` is the real duration of that epoch in a
population that has grown exponentially at rate `ρ`. Otherwise `G` may be evaluated where
`1 + ρ u ≤ 0` and the value need not be a real time: for `n = 2`, `ρ = -1` and `T_2(ω) = 1`,
`G(1) = 0` by `log 0 = 0`, while the cumulative intensity `R(s) = 1 - exp(-s)` never reaches `1`.
