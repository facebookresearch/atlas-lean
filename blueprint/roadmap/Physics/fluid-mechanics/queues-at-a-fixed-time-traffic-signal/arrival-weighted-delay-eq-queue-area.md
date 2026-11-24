# Total delay of the arrivals equals the queue area

Let `0 < λ < μ` (arrival and service rates), `R ≥ 0` and `G ≥ 0` (red and green durations), with the
strict capacity condition `λ (R + G) < μ G`. With the cumulative [arrivals](arrivals.md)
`A(s) = λ s` and [departures](departures.md) `D(s) = λ s - Q(s)` and the virtual delay
`d(s) = inf {δ ≥ 0 : A(s) ≤ D(s + δ)}` (`∞` for an empty set) of the vehicle arriving at time `s`,
the integral of `d(s)` over the arrival times `s ∈ [0, R + G)` against the arrival measure `λ ds`
equals the [queue area](queue-len-integral-cycle.md) `∫_0^{R+G} Q(t) dt`: the total waiting of the
vehicles arriving in the cycle is the time integral of the queue length. The integral of the delay
is taken in `[0, ∞]`.
