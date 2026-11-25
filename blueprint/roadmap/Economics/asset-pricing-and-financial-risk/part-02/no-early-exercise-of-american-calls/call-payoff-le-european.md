# European call value ≥ exercise value for risk-neutral p and R ≥ 1

Let `0 ≤ p ≤ 1` and `R ≥ 1` satisfy the risk-neutral (martingale) condition
`p u + (1 - p) d = R`, and let the strike be `K ≥ 0`; `S₀`, `u` and `d` are any real numbers.
On the binomial tree with stock price `S = S₀ u^(number of up moves) d^(number of down moves)`
at a node, value the European call by backward induction with up probability `p` and discount
factor `R⁻¹`: `max(S - K, 0)` with no period left, and `R⁻¹ (p V_up + (1 - p) V_down)` from the
values `V_up`, `V_down` at the two successor nodes otherwise. Then, at every node and with any
number `k` of periods left, this value is at least the immediate exercise value `max(S - K, 0)`.
