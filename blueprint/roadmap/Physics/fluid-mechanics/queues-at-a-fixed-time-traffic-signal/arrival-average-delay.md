# Average delay of the vehicles arriving in a clearing cycle

Let `0 < λ < μ` (arrival and service rates), `R ≥ 0` and `G ≥ 0` (red and green durations), with the
strict capacity condition `λ (R + G) < μ G`. With the cumulative [arrivals](arrivals.md)
`A(s) = λ s` and [departures](departures.md) `D(s) = λ s - Q(s)` and the virtual delay
`d(s) = inf {δ ≥ 0 : A(s) ≤ D(s + δ)}` (`∞` for an empty set) of the vehicle arriving at time `s`,
the integral of `d(s)` over `s ∈ [0, R + G)` against the arrival measure `λ ds`, divided by the
arrival volume `λ (R + G)`, equals `R² μ / (2 (μ - λ)(R + G))`: the mean first-in first-out delay of
the vehicles arriving in the cycle. The quotient is taken in `[0, ∞]`.
