# Cost-of-carry forward price from state prices

Let `ψ(ω)` be state prices (of any sign) on a finite state space and `R ≠ 0` a gross riskless
rate. If `ψ` prices the riskless unit payoff at `1 / R` (`∑_ω ψ(ω) = 1 / R`), prices the
underlying, which pays the terminal spot price `S(ω)` plus a known terminal income `inc`, at
the spot price `S0` (`∑_ω ψ(ω) (S(ω) + inc) = S0`), and prices the forward, with payoff
`S(ω) - F` and zero entry cost, at `0` (`∑_ω ψ(ω) (S(ω) - F) = 0`), then
`F = (S0 - inc / R) R`: the spot price less the present value of the income, grossed up at
`R`.
