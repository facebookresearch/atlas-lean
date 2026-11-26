# The heat semigroup's generator is the Laplacian, in `ENNReal`

Let `1 ≤ p < ∞` and let
`φ` be a compactly supported `C²` function on `EuclideanSpace ℝ (Fin n)`. Then
`eLpNorm (heatConvolution n φ t - φ - t * Δφ) p volume / t → 0` as `t → 0⁺`: the right-hand
difference quotient `(heatConvolution n φ t - φ) / t` converges to `Δφ` in `L^p`. This
`ENNReal`-valued form is the genuine `L^p` statement: `ENNReal.toReal` sends `⊤` to `0`, so a
real-valued limit alone could report convergence even when the remainder is not in `L^p`.
