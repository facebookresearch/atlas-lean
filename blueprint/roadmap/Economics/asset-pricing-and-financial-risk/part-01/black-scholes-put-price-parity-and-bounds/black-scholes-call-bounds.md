# Black Scholes Call bounds

Static bounds for the call (FI17.T02): `max (S0 - K e^{-rT}) 0 ≤ C ≤ S0`.
The upper bound is algebra from `0 ≤ Φ ≤ 1`. The lower bound `0 ≤ C` holds
because `C` is the discounted expectation of the nonnegative payoff
`max (x - K) 0` (`discounted_integral_call_riskNeutralLaw`); the lower bound
`S0 - K e^{-rT} ≤ C` is put nonnegativity through parity, and
`P(S0, K, r) = e^{-rT} C(K, S0, -r)` reduces put nonnegativity to call
nonnegativity.
