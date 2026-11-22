# Clear Denominators

Clearing denominators of nonnegative ratios: for `r e = a / b ≥ 0` in lowest terms, the
natural number `a * (D / b)`, where `D = commonDenominator r`; it equals `D * r e`
(`clearDenominators_cast`). A negative ratio, which the results below exclude by hypothesis, has
`a.toNat = 0` and is sent to `0`.
