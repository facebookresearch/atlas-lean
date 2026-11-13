# One-step no-arbitrage condition

**One-step no-arbitrage condition** (Atlas roadmap FI12.T01). For `S₀ > 0` and `0 < d < u`,
there is no one-step arbitrage iff `d < R < u`.

Proof route (not mandatory): if `R ≤ d`, `(Δ, B) = (1, -S₀)` is an arbitrage (cost `0`,
payoffs `(u - R) * S₀ ≥ 0` and `(d - R) * S₀ ≥ 0`, one of them positive since `d < u`);
if `u ≤ R`, `(Δ, B) = (-1, S₀)` is an arbitrage. Conversely, if `d < R < u`, the
risk-neutral weights `q = (R - d) / (u - d)` and `1 - q` are both positive, and the
`q`-weighted payoff of any portfolio is `R * (Δ * S₀ + B)` (since
`q * u + (1 - q) * d = R`), so a nonpositive-cost portfolio with nonnegative payoffs, one
positive, would have both a positive and a nonpositive `q`-weighted payoff: contradiction.
Use `linarith`/`nlinarith`; do not reprove the FTAP (this is a direct two-state argument).
