# Exact calibration at attainable levels

If the count `X` has law `ν` under `μ`, the
upper-tail p-value is exactly calibrated at every attainable level `s = upperTail ν k`:
`μ {upperTailPValue ν X ≤ s} = s`. Between attainable levels it is conservative
(`isValidPValue_upperTailPValue`).

## Sources

- Lehmann–Romano (2005), Lemma 3.3.1.
