# Binomial-tree hedge ratio at one step is the delta hedge

For any real `S₀`, `u`, `d`, `R` and any claim `V` on histories of moves whose payoff is `Cu`
after a single up move and `Cd` after a single down move, the delta-hedging ratio of `V` at the
root for horizon `1`, `(Cu - Cd) / (u * S₀ - d * S₀)`, equals the one-step delta hedge
`Δ = (Cu - Cd) / ((u - d) * S₀)`. No nonvanishing hypothesis is needed: both sides are the same
quotient, with the convention x / 0 = 0 when `(u - d) * S₀ = 0`.
