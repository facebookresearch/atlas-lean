# Kimura two-parameter transition matrix

Nucleotides are indexed `0 = A`, `1 = C`, `2 = G`, `3 = T`, so a substitution is a transition
(`A ↔ G`, `C ↔ T`) exactly when the two indices have the same parity. For real numbers `a` and `b`,
the Kimura matrix `T(a, b)` is the `4 × 4` matrix with entries
`1/4 + 1/4 · e^(-4b) + 1/2 · e^(-2(a + b))` on the diagonal,
`1/4 + 1/4 · e^(-4b) - 1/2 · e^(-2(a + b))` for a transition and `1/4 - 1/4 · e^(-4b)` for each
transversion (Kimura 1980, eqs. (5)–(6)). In the model, `a = α t` is the transition rate times time
and `b = β t` the rate of each of the two transversions times time. It is defined for all real `a`
and `b`; its rows [sum to one](sum-kimura-prob.md) and, for `a, b ≥ 0`, its entries are
[nonnegative](kimura-prob-nonneg.md).
