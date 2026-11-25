# Backward-induction value at one step is the risk-neutral price

For any real `u`, `d`, `R` and any claim `V` on histories of moves whose payoff is `Cu` after a
single up move and `Cd` after a single down move, the backward-induction value of `V` at the root
with one period left equals the one-step risk-neutral price `(q * Cu + (1 - q) * Cd) / R`, where
`q = (R - d) / (u - d)`. No condition on `u`, `d`, `R` is needed: both sides use the convention
x / 0 = 0.
