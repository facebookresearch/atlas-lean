# Kingman holding times after the exponential-growth time change

Let `T_k` (`k ∈ ℕ`) be
[Kingman holding times](../kingman-s-coalescent-and-watterson-s-estimator/kingman-times.md) of a
sample of size `n` under a measure `μ` on `Ω`: for `2 ≤ k ≤ n`, `T_k` has the exponential law
with rate `C(k, 2)` under `μ`, and `T_2, …, T_n` are independent. For a real number `ρ`, a
natural number `k` and `ω ∈ Ω`, let

`T^ρ_k(ω) = G(V_k(ω)) - G(V_{k+1}(ω))`, where `V_k(ω) = ∑_{j=k}^{n} T_j(ω)`,

be the [holding time under exponential growth](growth-holding.md) of the sequence
`(T_j(ω))_{j ∈ ℕ}`, with the [time change](growth-time.md) `G` at rate `ρ`. For `2 ≤ k ≤ n` it
depends only on `T_k, …, T_n`, and for `k > n` it is `0`. With `ρ ≥ 0` and `2 ≤ k ≤ n`,
`T^ρ_k` is the real duration of the epoch with `k` lineages in the genealogy of a sample from a
population that has grown exponentially at rate `ρ`. There, for `μ`-almost every `ω`, `G` is
only evaluated at nonnegative points ([positivity of the holding times](ae-t-pos.md)), where
`1 + ρ u > 0`; at points with `1 + ρ u ≤ 0` it follows the logarithm conventions
`log x = log |x|` and `log 0 = 0`.
