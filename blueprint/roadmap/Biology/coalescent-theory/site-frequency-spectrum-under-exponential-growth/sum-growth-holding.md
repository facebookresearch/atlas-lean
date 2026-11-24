# Real time to the most recent common ancestor under the time change

For every real number `ρ`, natural number `n` and real numbers `T_j` (`j ∈ ℕ`), the
[holding times under exponential growth](growth-holding.md) `T^ρ_k` satisfy

`∑_{k=2}^{n} T^ρ_k = G(∑_{k=2}^{n} T_k)`,

where `G` is the [time change](growth-time.md) for exponential growth at rate `ρ`; for `n < 2`
both sides are `0` (empty sums, and `G(0) = 0`). For `n ≥ 2`, `ρ ≥ 0` and `T_j ≥ 0` for
`2 ≤ j ≤ n` (as for Kingman's holding times, almost surely), the left side is the real time to
the most recent common ancestor, and the identity says that it is the time change of the
standard one. For other inputs the identity still holds, but `G` may be evaluated where
`1 + ρ u ≤ 0` and its value need not be a real time: for `n = 2`, `ρ = -1` and `T_2 = 1`,
`G(1) = 0` by `log 0 = 0`, while the cumulative intensity `R(s) = 1 - exp(-s)` never reaches `1`.
