# The $X$-coordinate of the Tate curve at the origin

Tate's coordinate
`X(u, q) = ∑_{n ∈ ℤ} qⁿu / (1 - qⁿu)² - 2 ∑_{n ≥ 1} n qⁿ / (1 - qⁿ)`, expanded at the origin
`u = 1` in the local parameter `T = u - 1`. It lies in `K⟦q⟧((T))`: the outer Laurent variable is
the local parameter `T`, and the inner power-series variable is `q`. Explicitly it is
`T⁻² + T⁻¹ + ∑_{k ≥ 0} c_k Tᵏ`, where `c_k ∈ K⟦q⟧` has constant term `0` and, for `M ≥ 1`,
`qᴹ`-coefficient `∑_{e ∣ M} e (e.choose k + (-1)ᵏ (e + k - 1).choose k)`, minus
`2σ₁(M) = 2 ∑_{e ∣ M} e` when `k = 0`. The pole bound (no term below `T⁻²`, and
`T⁻²`-coefficient `1`) is `coeff_tateOriginX_of_lt` and `coeff_tateOriginX_neg_two`; that
`(tateOriginX K, tateOriginY K)` satisfies the Weierstrass equation of the Tate curve is not
formalized.
