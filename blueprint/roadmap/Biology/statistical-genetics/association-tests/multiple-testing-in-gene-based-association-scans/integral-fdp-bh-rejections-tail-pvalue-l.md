# FDR control for tail-calibrated rare-variant tests

If the family `(T, G)` is
tail-calibrated with true nulls `H0` (`IsTailCalibratedFamily`: measurable statistics, antitone
reference tails, and for every null gene a reference tail dominating the true null tail) and its
p-values are PRDS on `H0`, then the Benjamini–Hochberg procedure at level `q ∈ [0, 1]` has false
discovery rate at most `q |H0| / m`.

## Sources

- Benjamini & Yekutieli (2001), Theorem 1.2, applied through `integral_falseDiscoveryProportion_bhRejections_le_of_isPRDSOn`.
