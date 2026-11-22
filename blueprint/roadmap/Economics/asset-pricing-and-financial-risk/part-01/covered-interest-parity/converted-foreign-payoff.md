# Converted Foreign Payoff

Terminal domestic payoff of the covered foreign strategy: convert one unit of
domestic currency to `1 / spot` units of foreign currency, invest at the foreign
gross return, and convert the proceeds back at the locked-in forward rate:
`forward * foreignGross / spot`. For nonzero `spot` and `foreignGross` it equals
the domestic deposit payoff only when covered interest parity holds
(`coveredInterestParity_iff`).
