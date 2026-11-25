# Kernel of the block-count drift

For a natural number `b` and a real `x`, the drift kernel is
`D_b(x) = ∑_{k=2}^b (k - 1) C(b, k) x^(k - 2) (1 - x)^(b - k)`, with natural-number powers (so
`0⁰ = 1`); for `b < 2` the sum is empty and `D_b = 0`. For a finite measure `Λ` on `[0, 1]` it
gives the [block-count drift](block-drift.md) as `γ_b = ∫ D_b dΛ`
([integral form](block-drift-eq-integral.md)).
