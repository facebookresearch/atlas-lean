# Add Valuation algebra Map

For a prime `p`, a perfect field `k` of characteristic `p` and a Witt vector `x : 𝕎 k`, the
`p`-adic additive valuation of the image of `x` in `K(p, k)` is the additive valuation
`IsDiscreteValuationRing.addVal (𝕎 k) x : ℕ∞` of `x` in the discrete valuation ring `𝕎 k`,
mapped to `WithTop ℤ` by `ENat.map` of the cast `ℕ → ℤ`.
