# Incompatible spaces (boundary case)

The quadratic reaction term `u ↦ u²` does not map
`L²(0, 1)` into itself: `u x = x ^ (-1/3)` is square integrable on `(0, 1)` but `u²` is not.
So `(X, F) = (L²(0, 1), u ↦ u²)` does not satisfy the hypotheses of `exists_isMildSolution`
(there is no map `F : X → X` at all); this is why the frozen phase space is `C(Ω̄)`.
