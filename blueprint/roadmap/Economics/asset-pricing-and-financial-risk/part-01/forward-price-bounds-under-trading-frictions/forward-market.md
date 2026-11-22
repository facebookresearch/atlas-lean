# One-period forward market with trading frictions

A one-period forward market with frictions consists of six real numbers: the spot bid price
`bid` (proceeds per unit of the underlying sold short), the spot ask price `ask` (cost per
unit bought), the gross lending rate `R_l` and the gross borrowing rate `R_b` over the
forward's life, the known income `I` that one unit of the underlying pays at maturity (a
deterministic dividend or carry, paid by a short seller to the lender of the asset), and the
forward price `F`, the delivery price of a forward contract on one unit with the same
maturity. No sign or ordering condition is imposed on them.
