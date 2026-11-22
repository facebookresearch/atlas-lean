# Strict Anti On cash Flow Price

With nonnegative payments and at least one positive payment at a date
`t ≥ 1`, the price is strictly decreasing in the yield on `(-1, ∞)`
(Atlas roadmap FI03.T02). The `1 ≤ t` condition is load-bearing: a positive
payment at `t = 0` alone is discounted by 1 at every yield. This is the bond /
present-value form over an arbitrary finite payment set; FI02.T02
`strictAntiOn_npv` is the separate NPV form over the fixed dates
`range (N + 1)`.
