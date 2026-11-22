# A locally optimal holding implies the consumption pricing equation

Take a finite state space with real weights `π(ω)`, a period utility `u`, a time-discount
factor `β`, endowments `e0` at date 0 and `e1(ω)` at date 1, and an asset with date-0 price `p`
and date-1 payoff `X(ω)`. Suppose the holding `ξ` is a local maximum over all real holdings of
`U(ξ) = u(e0 - ξ p) + β ∑_ω π(ω) u(e1(ω) + ξ X(ω))`, that `u` is differentiable at the
consumption levels `c0 = e0 - ξ p` and `c1(ω) = e1(ω) + ξ X(ω)` for every `ω`, and that
`u'(c0) ≠ 0`. Then `p = ∑_ω π(ω) m(ω) X(ω)` with the stochastic discount factor
`m(ω) = β u'(c1(ω)) / u'(c0)`; when `π` is a probability vector this is `p = E[m X]`.
