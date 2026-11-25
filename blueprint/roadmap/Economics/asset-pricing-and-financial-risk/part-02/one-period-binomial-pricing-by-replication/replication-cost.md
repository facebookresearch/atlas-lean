# Replication cost of a one-step claim

The replication cost of the one-step claim paying `Cu` in the up state and `Cd` in the down
state is the initial capital `Δ * S₀ + B` of the delta-and-bond replicating portfolio, with
delta hedge `Δ = (Cu - Cd) / ((u - d) * S₀)` and bond holding
`B = (u * Cd - d * Cu) / ((u - d) * R)` (stock worth `S₀` today and `u * S₀` or `d * S₀` at
expiry, bond worth `1` today and `R` at expiry). It is defined for all real values, with the
convention x / 0 = 0 in `Δ` and `B`.
