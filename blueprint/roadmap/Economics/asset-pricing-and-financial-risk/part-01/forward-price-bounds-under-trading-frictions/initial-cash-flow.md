# Initial cash flow of a static strategy

In a forward market with spot bid price `bid` and ask price `ask`, the cash received at time
`0` by a static strategy `(x, y, L, B, f)` (units bought at the ask, units sold short at the
bid, cash lent, cash borrowed, long forward units) is `bid · y + B - ask · x - L`: short-sale
proceeds and borrowing, minus purchases and lending (forwards cost nothing to enter).
