# Polynomial f2 map of the three-population admixture graph

The map `ℝ^5 → ℝ^3` from the parameters `(α, s, a, b, c)`, an admixture proportion `α`, the stem
length `s`, the lengths `a` and `b` of the `A` and `B` edges and the length `c` of the private edge
of `C`, given by `(α, s, a, b, c) ↦ (a + b, (1 - α) ^ 2 * (a + b) + c, α ^ 2 * (a + b) + c)`. It is
a polynomial map defined for all real parameters and does not depend on `s`. For nonnegative
lengths `s, a, b, c` and every real `α`, its value is the vector `(f2(A, B), f2(A, C), f2(B, C))`
of every [drift model on four edges with these weights and lengths](three-pop-f2-eq-f2.md), and such
a model exists. For other parameters it need not be an f2 vector: at `a = -1`, `b = c = 0` its
first component is `-1`, while f2 statistics are nonnegative. The [admissible](is-admissible.md)
parameters, with `α` an admixture proportion, are `0 ≤ α ≤ 1` and `s, a, b, c ≥ 0`.
