# Expected first-coalescence time under a bottleneck

Let `T_k` (`k ∈ ℕ`) be
[Kingman holding times](../kingman-s-coalescent-and-watterson-s-estimator/kingman-times.md)
of a sample of size `n` under a measure `μ` on `Ω`: for `2 ≤ k ≤ n`, `T_k` has the exponential
law with rate `C(k, 2)` under `μ`, and `T_2, …, T_n` are independent.
Suppose `n ≥ 2` and each `T_k` (`k ∈ ℕ`) is measurable, and let `a ≥ 0`, `d ≥ 0` and `f > 0` be
real numbers. Then the [time-changed holding time](bottleneck-times.md) of the most recent
epoch (`n` lineages) has mean

`∫ T^b_n dμ = c_n(η) = ∫_0^∞ exp(-C(n, 2) R_η(s)) ds`,

the [expected time to the first coalescence](../site-frequency-spectrum-under-variable-populatio/first-coal-mean.md)
among `n` lineages for the [bottleneck history](bottleneck-size.md) `η`, with its
[cumulative coalescence intensity](cum-rate-bottleneck-size.md) `R_η` (`μ` is a probability
measure, since `n ≥ 2`). This follows from `E[X] = ∫_0^∞ P(X > t) dt` for `X = T^b_n = G(T_n)`,
which is nonnegative `μ`-almost everywhere, and from
`P(G(T_n) > t) = P(T_n > R_η(t)) = exp(-C(n, 2) R_η(t))` for `t ≥ 0`.
