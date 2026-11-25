# American and European calls coincide for risk-neutral p and R ≥ 1

No early exercise for an American call on a non-dividend binomial stock: let `0 ≤ p ≤ 1` and
nonnegative interest `R ≥ 1` satisfy the risk-neutral (martingale) condition
`p u + (1 - p) d = R`, and let the strike be `K ≥ 0` (`S₀`, `u`, `d` are any real numbers). With
up probability `p` and discount factor `R⁻¹`, the American value of the call with exercise payoff
`max(S - K, 0)` (the Snell envelope: the payoff with no period left, otherwise the larger of the
payoff and the discounted expected value one period later) equals its European value (no
exercise before the horizon) at every node and with any number of periods left.
