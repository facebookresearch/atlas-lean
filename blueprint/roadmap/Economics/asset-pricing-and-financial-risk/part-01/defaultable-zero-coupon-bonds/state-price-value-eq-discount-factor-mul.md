# Loss-adjusted pricing of a defaultable zero-coupon bond

The state-price value of the
defaultable payoff equals `D * N * (1 - q_D * (1 - R))`: the risk-free value `D * N` minus
`D * N * q_D * (1 - R)`, the state-price value of the loss `(1 - R) * N` incurred in the
default states. On a nonempty state space with positive state prices this term is the
discounted risk-neutral expected loss `D * (q_D * (1 - R) * N)`, not the undiscounted
expected loss; it is a nonnegative loss when also `0 ≤ R ≤ 1` and `0 ≤ N`. The identity
itself holds for every `R`, `N`, and state-price vector with `D ≠ 0`.
