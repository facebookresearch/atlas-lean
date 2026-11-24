# Mean time to the first coalescence under exponential growth

Let `n ≥ 2` and `ρ ≥ 0`. Let `T_k` (`k ∈ ℕ`) be
[Kingman holding times](../kingman-s-coalescent-and-watterson-s-estimator/kingman-times.md) of a
sample of size `n` under a measure `μ` on `Ω`: for `2 ≤ k ≤ n`, `T_k` has the exponential law
with rate `C(k, 2)` under `μ`, and `T_2, …, T_n` are independent.
Suppose each `T_k` (`k ∈ ℕ`) is measurable. As `n ≥ 2`, `μ` is a probability measure. The
[time-changed holding time](growth-times.md) `T^ρ_n` of the most recent epoch, with `n`
lineages, has mean Bhaskar–Song's
[first-coalescence time](../site-frequency-spectrum-under-variable-populatio/first-coal-mean.md) for the
[relative size](exp-growth-size.md) `η(s) = exp(-ρ s)` (Griffiths & Tavaré):

`E[T^ρ_n] = c_n(η) = ∫_0^∞ exp(-C(n, 2) R(s)) ds`,

where `R(s) = ∫_0^s exp(ρ r) dr` is the
[cumulative coalescence intensity](../site-frequency-spectrum-under-variable-populatio/cum-rate.md).
The integral converges: `R(s) ≥ s` for `s ≥ 0`, so the integrand is at most `exp(-C(n, 2) s)`.
The proof uses the tail formula `E[X] = ∫_0^∞ μ(X > t) dt` for `X = T^ρ_n = G(T_n)`, which is
nonnegative almost everywhere, and, for `t ≥ 0`,
`μ(G(T_n) > t) = μ(T_n > R(t)) = exp(-C(n, 2) R(t))`.
