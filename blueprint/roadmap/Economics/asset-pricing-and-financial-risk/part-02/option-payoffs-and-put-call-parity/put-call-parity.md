# Put Call Parity

Put-call parity for replicable European claims. `price` is an additive
pricing functional on terminal payoffs (functions of the terminal underlying
`ω`): an additive homomorphism `(ℝ → ℝ) →+ ℝ`, so the price of a difference of
payoffs is the difference of their prices (`map_sub`). Hypotheses:

* `_hR`: the gross risk-free return `R` is positive. The algebra below does not
  use it (hence the underscore); it excludes `R = 0`, where Lean's `K / 0 = 0`
  would let the zero functional satisfy `hBond`.
* `hStock`: the price of the terminal-underlying payoff is `S0 - D`, where
  `S0` is today's spot and `D` is the present value of dividends paid over the
  option's life (dividend convention: the holder of the replicating stock
  position receives the dividends, so the ex-dividend stock price `S0 - D`
  prices the terminal payoff alone).
* `hBond`: the price of the constant payoff `K` is `K / R`, the strike
  discounted at the gross risk-free return `R`.
* `hC`, `hP`: `C` and `P` are the prices of the call and put payoffs.

Conclusion: `C - P = (S0 - D) - K / R`. No no-arbitrage theorem is reproved:
the law of one price is the additivity of `price` plus the payoff identity,
applied once.
