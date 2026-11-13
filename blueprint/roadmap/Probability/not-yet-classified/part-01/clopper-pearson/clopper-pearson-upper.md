# Clopper–Pearson upper endpoint

**Clopper–Pearson upper endpoint** after `x` successes in `n` trials at level `α`:
`U(x) = sup {p ∈ [0, 1] | α / 2 ≤ P_p(X ≤ x)}`, where `P_p(X ≤ x) = 1 - binomTail n (x + 1) p`.
For `0 < α < 2` and `x < n` it is the root of `P_p(X ≤ x) = α / 2`
(`binomTail_clopperPearsonUpper`); `U(n) = 1` (`clopperPearsonUpper_self`).
