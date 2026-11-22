# Put–call parity for an additive pricing functional

Put-call parity for replicable European claims. Let `price` be an additive pricing functional on
terminal payoffs, the real functions `f` of the terminal underlying price `ω`: the price of a sum
of payoffs is the sum of their prices, so the price of a difference is the difference of the
prices. Let `S0`, `D`, `K`, `R`, `C`, `P` be real numbers with:

* `R > 0`, the gross risk-free return;
* the stock condition `price(ω ↦ ω) = S0 - D`, where `S0` is today's spot and `D` is the present
  value of dividends paid over the option's life (dividend convention: the holder of the
  replicating stock position receives the dividends, so the ex-dividend stock price `S0 - D`
  prices the terminal payoff alone);
* the bond condition `price(ω ↦ K) = K / R`: the constant payoff `K` costs the strike discounted
  at the gross risk-free return;
* `C = price(ω ↦ max(ω - K, 0))` and `P = price(ω ↦ max(K - ω, 0))`, the prices of the call and
  put payoffs.

Then `C - P = (S0 - D) - K / R`. The law of one price is the additivity of `price` plus the
payoff identity `max(ω - K, 0) - max(K - ω, 0) = ω - K`, applied once. The identity does not use
`R > 0`; that assumption excludes `R = 0`, where the convention x / 0 = 0 would give `K / R = 0`,
so the bond condition would price the payoff `K` at `0` and the zero functional would satisfy it.
