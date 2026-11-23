# The delta-method variance of Tajima's `D` is `1`

**The delta-method variance of Tajima's `D` is `1`** under the neutral model, for `n ≥ 4`
genes and `θ > 0`, under the hypotheses of Tajima's variance identity
`KingmanTimes.variance_tajimaNumerator`. With `N = π - S / a₁`, `V = e₁ S + e₂ S (S - 1)` and
`v = c₁ θ + c₂ θ²`: the map `(x, y) ↦ x / √y` has derivative `L = (√v)⁻¹ • fst` at the mean point
`(E N, E V) = (0, v)`, and the linearization `L (N - E N, V - E V)` has variance `1`.
