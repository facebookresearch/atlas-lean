# Benjamini–Hochberg FDR control for super-uniform nulls

If the p-values are independent
and every true-null p-value is valid (super-uniform: `μ {p i ≤ t} ≤ t` for `t ∈ [0, 1]`), the BH
procedure at level `q ∈ [0, 1]` has false discovery rate at most `q |H0| / m`. Properly
calibrated discrete p-values, such as those of permutation or exact tests, are included. Nothing
is assumed about the false-null p-values beyond measurability and independence. (For `m = 0`
both sides are `0`.)

## Sources

- Benjamini & Hochberg (1995), Theorem 1, whose proof uses only `P(p_i ≤ t) ≤ t` for the true nulls.
