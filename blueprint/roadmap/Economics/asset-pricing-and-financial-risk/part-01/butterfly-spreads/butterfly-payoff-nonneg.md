# Butterfly Payoff nonneg

A butterfly payoff is nonnegative when `K1 ≤ K2 ≤ K3` and
`K1 + K3 ≤ 2 * K2`. Under the ordering, the inequality is also necessary for
nonnegativity at every terminal price: at and above `K3` the payoff is the
constant `2 * K2 - K1 - K3`. With `K2` the midpoint (`K1 + K3 = 2 * K2`) that
constant is `0`, so the payoff additionally vanishes above `K3`. The inequality
cannot be dropped: with `K1 = 0, K2 = 1, K3 = 100` the payoff at `S = 100` is
`-98`.
