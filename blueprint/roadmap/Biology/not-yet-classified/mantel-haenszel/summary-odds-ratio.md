# Summary Odds Ratio

The Mantel–Haenszel summary odds ratio `R = ∑_k (A_k D_k / T_k) / ∑_k (B_k C_k / T_k)`, a
cross-product estimator of a common odds ratio (not a risk ratio: for one table with
`(A, B, C, D) = (4, 2, 1, 3)` it is `6`, while the risk ratio is `2`). It is meaningful when every
total `T_k` and the denominator `∑_k B_k C_k / T_k` are positive; a zero denominator gives `0` by
Lean's convention `x / 0 = 0`.
