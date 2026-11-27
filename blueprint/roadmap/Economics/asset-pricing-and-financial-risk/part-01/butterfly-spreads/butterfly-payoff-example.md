# Numerical example of a nonnegative butterfly payoff

With strikes `90`, `100`, `110` and terminal price `105`, the long butterfly payoff is
`max(105 - 90, 0) - 2 max(105 - 100, 0) + max(105 - 110, 0) = 15 - 10 + 0 = 5 ≥ 0`.
