# Growth Time

The **Griffiths–Tavaré time change** for exponential growth: the real time
`G(u) = log(1 + ρ u) / ρ` (and `G(u) = u` when `ρ = 0`) at which the cumulative coalescence
intensity `R(s) = ∫_0^s 1/η = (exp(ρ s) - 1) / ρ` reaches `u` (`cumRate_growthTime`). A
standard-coalescent event at time `u` happens at real time `G(u)`. Meaningful for
`1 + ρ u > 0`.
