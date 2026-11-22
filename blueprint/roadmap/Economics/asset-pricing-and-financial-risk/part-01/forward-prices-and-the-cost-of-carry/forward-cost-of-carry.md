# Forward cost of carry

Replicating a forward with borrowing and the underlying
yields the frozen cost-of-carry price: if state prices `ψ` price the riskless unit
payoff at `1 / R`, price the underlying (spot plus known terminal income `inc`) at `S0`,
and price the forward (payoff `S ω - F`, zero entry cost) at `0`, then
`F = (S0 - inc / R) * R`, i.e. the spot price less the present value of the income,
grossed up at `R`.
Related landed result: `Domains.Economics.Finance.ForwardPriceBounds`
proves the same frictionless price by collapsing a no-arbitrage interval; this
theorem proves it by the distinct replication + state-price (law-of-one-price)
route of roadmap FI10.T01.
