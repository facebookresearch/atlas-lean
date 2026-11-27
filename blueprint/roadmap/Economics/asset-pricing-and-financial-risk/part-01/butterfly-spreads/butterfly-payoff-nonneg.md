# Butterfly payoff is nonnegative for K₁ ≤ K₂ ≤ K₃ with K₁ + K₃ ≤ 2K₂

For strikes `K1 ≤ K2 ≤ K3` with `K1 + K3 ≤ 2 K2` and every terminal price `S`, the long butterfly
payoff `max(S - K1, 0) - 2 max(S - K2, 0) + max(S - K3, 0)` is nonnegative. Under the ordering,
the inequality is also necessary for nonnegativity at every terminal price: at and above `K3` the
payoff is the constant `2 K2 - K1 - K3`. With `K2` the midpoint (`K1 + K3 = 2 K2`) that constant
is `0`, so the payoff also vanishes above `K3`. The inequality cannot be dropped: with `K1 = 0`,
`K2 = 1` and `K3 = 100` the payoff at `S = 100` is `-98`.
