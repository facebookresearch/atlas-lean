# Bounds on the Black–Scholes call price

For `S0, K, σ, T > 0` and any real `r`, the Black–Scholes call price
`C = S0 Φ(d₁) - K e^{-rT} Φ(d₂)`, where `Φ` is the standard normal cdf,
`d₁ = (log (S0 / K) + (r + σ²/2) T) / (σ √T)` and `d₂ = d₁ - σ √T`, satisfies
`max(S0 - K e^{-rT}, 0) ≤ C ≤ S0`. The upper bound follows from `0 ≤ Φ ≤ 1`. The lower bound
`0 ≤ C` holds because `C` is the discounted expectation `e^{-rT} E[max(S_T - K, 0)]` of a
nonnegative payoff, for `S_T = S0 exp((r - σ²/2) T + σ √T Z)` with `Z` standard normal. The lower
bound `S0 - K e^{-rT} ≤ C` is the nonnegativity of the put price `P = K e^{-rT} Φ(-d₂) - S0 Φ(-d₁)`
through put–call parity `C - P = S0 - K e^{-rT}`, and `P(S0, K, r) = e^{-rT} C(K, S0, -r)` reduces
the nonnegativity of the put price to that of the call price.
