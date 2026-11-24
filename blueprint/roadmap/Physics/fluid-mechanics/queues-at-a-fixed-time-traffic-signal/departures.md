# Cumulative departures from the signal queue

For rates `λ`, `μ`, a red duration `R` and a time `s ≥ 0`, the cumulative departures are
`D(s) = max(λ s - Q(s), 0)`, the arrivals minus the vehicles still queued, with the
[signal queue](queue-len.md) `Q(t)` (`λ t` for `t ≤ R`, `max(0, λ R - (μ - λ)(t - R))` for `t > R`).
For `0 < λ < μ` the maximum is not needed: `D(s) = λ s - Q(s)`.
