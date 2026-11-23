# Polynomial f2 map of the three-population admixture graph

The map `ℝ^5 → ℝ^3` from the parameters `(α, s, a, b, c)`, an admixture proportion `α`, the stem
length `s`, the lengths `a` and `b` of the `A` and `B` edges and the length `c` of the private edge
of `C`, given by `(α, s, a, b, c) ↦ (a + b, (1 - α) ^ 2 * (a + b) + c, α ^ 2 * (a + b) + c)`. Its
value is the vector `(f2(A, B), f2(A, C), f2(B, C))` of the
[four-edge admixture drift model](three-pop-f2-eq-f2.md). It is a polynomial map defined for all
real parameters and does not depend on `s`; the [admissible](is-admissible.md) parameters are
`0 ≤ α ≤ 1` and `s, a, b, c ≥ 0`.
