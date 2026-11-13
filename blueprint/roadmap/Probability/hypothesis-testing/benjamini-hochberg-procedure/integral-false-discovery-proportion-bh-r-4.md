# Benjamini–Yekutieli FDR control under PRDS

If the p-values are PRDS on the set `H0` of
true nulls (`IsPRDSOn`) and every true-null p-value is valid (super-uniform:
`μ {p i ≤ t} ≤ t` for `t ∈ [0, 1]`), then the unmodified BH procedure at level `q ∈ [0, 1]` has
false discovery rate at most `q |H0| / m`. Nothing is assumed about the false-null p-values beyond
measurability and the joint PRDS condition. Independent p-values are PRDS
(`isPRDSOn_of_iIndepFun`), so this generalizes
`integral_falseDiscoveryProportion_bhRejections_le_of_isValidPValue`. (For `m = 0` both sides
are `0`.)

## Sources

- Benjamini & Yekutieli, *The control of the false discovery rate in multiple testing under dependency*, Ann. Statist. 29 (2001), 1165–1188, Theorem 1.2.
