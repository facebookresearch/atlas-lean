# Counterflow Hot Temp

Hot-stream temperature of the counterflow solution with the hot inlet `Thi` at `x = 0` and the
cold inlet `Tci` at `x = L`: `Th(x) = Thi - K / Ch * D₀ * ∫₀ˣ exp (-s y) dy`, where
`D₀ = counterflowInletDiff Ch Cc K L Thi Tci`. Intended for `Ch, Cc > 0`.
