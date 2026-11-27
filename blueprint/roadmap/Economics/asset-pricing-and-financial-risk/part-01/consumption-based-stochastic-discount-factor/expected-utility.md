# Investor's two-period utility from an asset position

An investor with period utility `u`, time-discount factor `β`, date-0 endowment `e0` and
date-1 endowment `e1(ω)` in state `ω` of a finite state space buys `ξ` units of an asset with
date-0 price `p` and date-1 payoff `X(ω)`. Date-0 consumption is `e0 - ξ p`, date-1 consumption
in state `ω` is `e1(ω) + ξ X(ω)`, and state `ω` has weight `π(ω)`. The investor's objective is
`U(ξ) = u(e0 - ξ p) + β ∑_ω π(ω) u(e1(ω) + ξ X(ω))`. When `π` is a probability vector this is
expected utility; the weights `π(ω)` may be any real numbers.
