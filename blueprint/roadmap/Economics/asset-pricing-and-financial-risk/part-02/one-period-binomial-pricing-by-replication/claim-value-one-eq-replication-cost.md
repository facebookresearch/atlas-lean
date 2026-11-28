# Backward-induction value at one step is the replication cost

Let `S₀ ≠ 0`, `u ≠ d` and `R ≠ 0`, and let `V` be a claim on histories of moves whose payoff is
`Cu` after a single up move and `Cd` after a single down move. The backward-induction value of
`V` at the root with one period left, `(q * Cu + (1 - q) * Cd) / R` with `q = (R - d) / (u - d)`,
equals the replication cost `Δ * S₀ + B`, where `Δ = (Cu - Cd) / ((u - d) * S₀)` and
`B = (u * Cd - d * Cu) / ((u - d) * R)`. This combines two facts: that value is the one-step
risk-neutral price, and the risk-neutral price equals the replication cost.
