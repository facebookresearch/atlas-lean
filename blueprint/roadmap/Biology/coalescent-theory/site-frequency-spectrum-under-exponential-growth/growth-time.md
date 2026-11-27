# Griffiths–Tavaré time change for exponential growth

For real numbers `ρ` and `u`, let

`G(u) = u` if `ρ = 0`, and `G(u) = log(1 + ρ u) / ρ` if `ρ ≠ 0`.

The logarithm follows the conventions `log x = log |x|` and `log 0 = 0`: for `ρ ≠ 0` and
`1 + ρ u ≤ 0` the value is `log |1 + ρ u| / ρ`, which is `0` when `1 + ρ u = 0`. The intended
domain is `1 + ρ u > 0`, which holds for instance when `ρ ≥ 0` and `u ≥ 0`. There `G(u)` is the
time at which the [cumulative coalescence intensity](../site-frequency-spectrum-under-variable-populatio/cum-rate.md)
`R(s) = ∫_0^s exp(ρ r) dr` of the [relative size](exp-growth-size.md) `η(r) = exp(-ρ r)`
reaches `u`: `R(G(u)) = u` ([inversion](cum-rate-growth-time.md)), where
`R(s) = (exp(ρ s) - 1) / ρ` for `ρ ≠ 0` and `R(s) = s` for `ρ = 0`. A standard-coalescent event
at standard time `u` happens at real time `G(u)`.
