# Discounted expected terminal price equals the spot

For `S0 > 0`, `T ≥ 0` and any real `r` and `σ`, the log-normal risk-neutral law `Q` of the
terminal price, the law of `S0 exp((r - σ²/2) T + σ √T Z)` with `Z` standard normal, has mean
`∫ x dQ(x) = S0 e^{rT}`, so the discounted expected terminal price `e^{-rT} ∫ x dQ(x)` is `S0`.
