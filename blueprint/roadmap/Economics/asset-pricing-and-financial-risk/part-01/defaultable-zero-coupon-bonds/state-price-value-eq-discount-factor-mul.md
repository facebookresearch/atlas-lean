# Loss-adjusted pricing of a defaultable zero-coupon bond

Take state prices `ψ(ω)` on a finite state space with risk-free discount factor
`D = ∑_ω ψ(ω) ≠ 0`, a set of default states with risk-neutral default probability
`q_D = (∑_{ω default} ψ(ω)) / D`, and a bond with face value `N` and recovery rate `R` (any
real numbers) that pays `R N` in the default states and `N` in the others. Its state-price
value is `∑_ω ψ(ω) · payoff(ω) = D N (1 - q_D (1 - R))`: the risk-free value `D N` minus
`D N q_D (1 - R)`, the state-price value of the loss `(1 - R) N` incurred in the default
states. When there is at least one state and all state prices are positive, this term is the
discounted risk-neutral expected loss `D · (q_D (1 - R) N)`, not the undiscounted expected
loss; it is nonnegative when also `0 ≤ R ≤ 1` and `N ≥ 0`.
