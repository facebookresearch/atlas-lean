# Cash-and-carry arbitrage above the upper bound

In a forward market with spot ask price `ask ≥ 0`, gross borrowing rate `R_b`, income `I` per
unit of the underlying paid at maturity and forward price `F > ask · R_b - I`, the
cash-and-carry strategy is an arbitrage: borrow `ask`, buy one unit of the underlying at the
ask and sell one unit forward. Its initial cash flow is `0` and its terminal cash flow is
`F - (ask · R_b - I) > 0`.
