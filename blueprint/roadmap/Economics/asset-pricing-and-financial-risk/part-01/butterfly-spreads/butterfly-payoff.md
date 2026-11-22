# Payoff of a long butterfly spread

For real strikes `K1`, `K2`, `K3` and terminal price `S`, the payoff at expiry of a long butterfly
spread (long one call at `K1`, short two calls at `K2`, long one call at `K3`) is
`max(S - K1, 0) - 2 max(S - K2, 0) + max(S - K3, 0)`. The formula places no order on the strikes;
the usual spread has `K1 < K2 < K3`.
