# Grid Duhamel

The **two-point discrete Duhamel operator** on a fixed grid of `k` times:
`gridDuhamel x y h j = ∑_{i ≤ j} (∏_{l < i} (1 + x l)) · h i · ∏_{i < l ≤ j} (1 + y l)`, the grid
analogue of `h ↦ ∫_{(0, t]} P(x)(0, s) dh(s) P(y)(s, t]`. On the diagonal it is T44's
`duhamelDeriv` (`gridDuhamel_self`), and it satisfies the exact Duhamel equation for
`prodIntegral` (`prodIntegral_sub_prodIntegral_eq_gridDuhamel`).
