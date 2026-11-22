# Funded-gains FTAP

Embed the funded gains `g a ω = X a ω - R * p a`
(payoff minus gross-risk-free-return times price) in the existing gain-form
FTAP: the funded gains admit no arbitrage iff there is a strictly positive
normalized `q` with `E_q[X a] = R * p a` for every asset (Atlas roadmap
FI08.T01). This does NOT reprove the FTAP; it applies
`one_period_fundamental_theorem_asset_pricing_general` to `g` and rewrites
`∑ ω, q ω * (X a ω - R * p a) = 0` as `∑ ω, q ω * X a ω = R * p a` using
`∑ ω, q ω = 1`. No sign hypothesis on `R` is needed: the equivalence is pure
algebra plus the FTAP.
