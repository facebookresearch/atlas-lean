# Forward Market

A one-period forward market with frictions. The underlying can be bought at the ask and sold
short at the bid; cash is lent at the gross rate `lendRate` and borrowed at the gross rate
`borrowRate` over the forward's life; one unit of the underlying pays the known income `income`
at maturity (a deterministic dividend or carry, paid by a short seller to the lender of the
asset); `forwardPrice` is the delivery price of a forward contract on one unit, of the same
maturity and unit.
