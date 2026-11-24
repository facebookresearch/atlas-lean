# Arrivals and departures of the signal queue form a flow pair

For `0 < λ < μ` and `R ≥ 0`, the cumulative [arrivals](arrivals.md) `A(s) = λ s` and
[departures](departures.md) `D(s) = λ s - Q(s)` form a lossless flow pair: both vanish at time `0`,
both are nondecreasing, and `D(s) ≤ A(s)` for every `s ≥ 0`. Their backlog `A(s) - D(s)` is the
[signal queue](queue-len.md) `Q(t)` (`λ t` for `t ≤ R`, `max(0, λ R - (μ - λ)(t - R))` for `t > R`)
at every `s ≥ 0`.
