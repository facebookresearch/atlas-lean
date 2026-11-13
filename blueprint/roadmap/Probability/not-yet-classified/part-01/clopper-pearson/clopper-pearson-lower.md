# Clopper–Pearson lower endpoint

**Clopper–Pearson lower endpoint** after `x` successes in `n` trials at level `α`:
`L(x) = inf {p ∈ [0, 1] | α / 2 ≤ P_p(X ≥ x)}`. For `0 < α < 2` and `1 ≤ x ≤ n` it is the root of
`P_p(X ≥ x) = α / 2` (`binomTail_clopperPearsonLower`); `L(0) = 0`
(`clopperPearsonLower_zero`).
