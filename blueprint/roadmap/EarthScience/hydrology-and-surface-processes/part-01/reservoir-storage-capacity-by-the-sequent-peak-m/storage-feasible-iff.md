# Storage is feasible exactly when capacity covers the worst deficit

Let a reservoir of capacity `C` start full, `S 0 = C`, and follow
`S (t + 1) = min C (S t + Q_t - R_t)` for `t < n`, with inflows `Q` and required releases `R` over
`n` time steps (no sign is assumed on `C`, `Q` or `R`). Then `S t ≥ 0` for every `t ≤ n` if and
only if `C` is at least the [worst required storage](worst-required-storage.md) `W`, the largest
net deficit over a window of consecutive steps. So `W` is the least capacity that meets every
release.
