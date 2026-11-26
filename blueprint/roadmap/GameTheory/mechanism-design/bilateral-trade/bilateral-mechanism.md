# Bilateral-trade mechanism

A deterministic bilateral-trade mechanism on reports:
`alloc s b ∈ {0, 1}` is the trade decision when the seller reports cost `s` and the buyer
reports value `b`, `payBuyer s b` is the price charged to the buyer and `paySeller s b` the
amount paid to the seller when trade occurs. No money changes hands without trade: `buyerUtil`
and `sellerUtil` are `0` when `alloc s b = 0`, whatever the two prices are there. The mechanism
is defined at all real reports; DSIC, efficiency, individual rationality and weak budget balance
constrain it only at reports in `[0, 1]`.
