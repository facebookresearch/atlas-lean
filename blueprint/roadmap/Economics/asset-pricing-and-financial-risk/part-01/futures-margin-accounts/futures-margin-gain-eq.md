# Futures Margin Gain eq

A zero-interest futures margin-account gain telescopes to the contract
multiplier times the total price change `F n - F 0`. This is
`Finset.mul_sum` plus `Finset.sum_range_sub`; do not reprove either.
