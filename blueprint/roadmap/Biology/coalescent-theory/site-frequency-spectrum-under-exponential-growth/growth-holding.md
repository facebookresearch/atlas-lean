# Holding times under exponential growth

For a real number `ρ`, a natural number `n`, real numbers `T_j` (`j ∈ ℕ`) and a natural number
`k`, let

`T^ρ_k = G(V_k) - G(V_{k+1})`,

where `V_k = ∑_{j=k}^{n} T_j` are the [epoch ends](epoch-end.md) and `G` is the
[time change](growth-time.md) for exponential growth at rate `ρ`. For `k > n` both epoch ends
are `0` and `T^ρ_k = 0`. The intended domain is `ρ ≥ 0` and `T_j ≥ 0` for `2 ≤ j ≤ n`: then,
for `2 ≤ k ≤ n`, `G` is evaluated at points `u ≥ 0`, where `1 + ρ u > 0`; at points with
`1 + ρ u ≤ 0` it follows the logarithm conventions `log x = log |x|` and `log 0 = 0`. The epoch
with `k` lineages lasts from `V_{k+1}` to `V_k` in standard time and `T^ρ_k` in real time.
When the `T_j` are Kingman's holding times, the `T^ρ_k` are the holding times of the genealogy
of a sample from a population that has grown exponentially at rate `ρ`: this time-change
representation is taken as the definition of the coalescent under exponential growth
(Griffiths & Tavaré).
