# Cost-of-carry forward price from state prices

Replicating a forward with borrowing and the underlying
yields the cost-of-carry price: if state prices `ψ` price the riskless unit
payoff at `1 / R`, price the underlying (spot plus known terminal income `inc`) at `S0`,
and price the forward (payoff `S ω - F`, zero entry cost) at `0`, then
`F = (S0 - inc / R) * R`, i.e. the spot price less the present value of the income,
grossed up at `R`.
