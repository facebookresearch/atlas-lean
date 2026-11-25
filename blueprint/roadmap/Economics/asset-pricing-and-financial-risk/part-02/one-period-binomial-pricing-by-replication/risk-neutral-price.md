# One-step risk-neutral price of a claim

For real `u`, `d`, `R`, the one-step risk-neutral price of a claim paying `Cu` in the up state
and `Cd` in the down state is `(q * Cu + (1 - q) * Cd) / R`, with risk-neutral up probability
`q = (R - d) / (u - d)`. Division follows the convention x / 0 = 0, so `q = 0` when `u = d` and
the price is `0` when `R = 0`.
