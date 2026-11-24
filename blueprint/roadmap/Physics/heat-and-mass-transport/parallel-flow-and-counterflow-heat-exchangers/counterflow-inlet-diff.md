# Counterflow Inlet Diff

Boundary constant of the counterflow solution: the temperature difference
`Th(0) - Tc(0) = (Thi - Tci) / (1 + K / Cc * ∫₀ᴸ exp (-s y) dy)` at the hot inlet, fixed by the
cold inlet condition `Tc(L) = Tci`, with `s = counterflowRate Ch Cc K`. The denominator is at
least `1` for `K, L ≥ 0` and `Cc > 0`.
