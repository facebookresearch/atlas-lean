# Hedge Ratio one eq delta Hedge

The landed delta-hedging ratio at horizon `1` is the one-step delta hedge: unfold
`hedgeRatio` (the `claimValue ... 0` terms are the payoffs, the `price` terms are
`u * S₀` and `d * S₀`) and use `u * S₀ - d * S₀ = (u - d) * S₀`. No nonvanishing
hypothesis is needed: both sides are the same quotient.
