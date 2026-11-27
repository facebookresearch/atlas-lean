# Cumulative variation-margin gain of a futures position

For a futures position with contract multiplier `m`, futures settlement prices
`F(0), F(1), F(2), …` and `n` daily settlements, the cumulative variation-margin gain is
`∑_{i=0}^{n-1} m (F(i+1) - F(i))`. Each daily settlement pays the multiplier times that day's
price change; there is no interest on the margin account.
