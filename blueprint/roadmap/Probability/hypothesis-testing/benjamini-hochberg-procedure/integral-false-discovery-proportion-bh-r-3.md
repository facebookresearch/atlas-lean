# Benjamini–Yekutieli FDR control under arbitrary dependence

If every true-null p-value is
valid (super-uniform: `μ {p i ≤ t} ≤ t` for `t ∈ [0, 1]`), then the BH procedure run at the
corrected level `q / H_m`, where `H_m = ∑_{k=1}^m 1/k` is the harmonic number, has false discovery
rate at most `q |H0| / m`, for any `q ∈ [0, 1]`. No independence, PRDS, or other assumption on the
joint law of the p-values is made: they may be arbitrarily dependent. The factor `H_m ≈ log m` is
the price paid relative to `integral_falseDiscoveryProportion_bhRejections_le_of_isValidPValue`,
which runs BH at level `q` but needs independence. (For `m = 0` both sides are `0`.)

## Sources

- Benjamini & Yekutieli, *The control of the false discovery rate in multiple testing under dependency*, Ann. Statist. 29 (2001), 1165–1188, Theorem 1.3.
