# The one-step binomial model is arbitrage-free iff d < R < u

For `S₀ > 0` and `0 < d < u` (and any real `R`), the one-step bond/stock model (bond price `1`
today and `R` at expiry; stock price `S₀` today and `u * S₀` in the up state or `d * S₀` in the
down state) has no one-step arbitrage, that is, no portfolio of cost at most `0` whose payoffs
are nonnegative in both states and positive in at least one, if and only if `d < R < u`.

Proof sketch: if `R ≤ d`, `(Δ, B) = (1, -S₀)` is an arbitrage (cost `0`,
payoffs `(u - R) * S₀ ≥ 0` and `(d - R) * S₀ ≥ 0`, one of them positive since `d < u`);
if `u ≤ R`, `(Δ, B) = (-1, S₀)` is an arbitrage. Conversely, if `d < R < u`, the
risk-neutral weights `q = (R - d) / (u - d)` and `1 - q` are both positive, and the
`q`-weighted payoff of any portfolio is `R * (Δ * S₀ + B)` (since
`q * u + (1 - q) * d = R`), so, as `R > d > 0`, a nonpositive-cost portfolio with nonnegative
payoffs, one positive, would have both a positive and a nonpositive `q`-weighted payoff:
contradiction.
