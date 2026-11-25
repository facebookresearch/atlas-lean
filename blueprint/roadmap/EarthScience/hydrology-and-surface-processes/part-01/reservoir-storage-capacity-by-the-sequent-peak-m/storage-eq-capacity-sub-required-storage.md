# Spill-capped storage is capacity minus the storage deficit

Let a reservoir of capacity `C` start full, `S 0 = C`, and follow
`S (t + 1) = min C (S t + Q_t - R_t)` for `t < n`, with inflows `Q` and required releases `R` over
`n` time steps: the spill is applied at the end of the step, after the release, and no sign is
assumed on `C`, `Q` or `R` (a negative `S t` records a shortfall). Then `S t = C - K_t` for every
`t ≤ n`, where `K_t` is the [storage deficit](required-storage-at.md) after `t` steps.
