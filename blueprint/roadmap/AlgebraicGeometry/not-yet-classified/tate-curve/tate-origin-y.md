# The $Y$-coordinate of the Tate curve at the origin

Tate's coordinate
`Y(u, q) = ∑_{n ∈ ℤ} (qⁿu)² / (1 - qⁿu)³ + ∑_{n ≥ 1} n qⁿ / (1 - qⁿ)`, expanded at the origin
`u = 1` in the local parameter `T = u - 1`, as an element of `K⟦q⟧((T))` with outer Laurent
variable `T` and inner power-series variable `q`. Explicitly it is
`-T⁻³ - 2T⁻² - T⁻¹ + ∑_{k ≥ 0} c_k Tᵏ`, where `c_k ∈ K⟦q⟧` has constant term `0` and, for
`M ≥ 1`, `qᴹ`-coefficient
`∑_{e ∣ M} (e.choose 2 · e.choose k - (e + 1).choose 2 · (-1)ᵏ (e + k - 1).choose k)`, plus
`σ₁(M) = ∑_{e ∣ M} e` when `k = 0`. The pole bound (no term below `T⁻³`, and
`T⁻³`-coefficient `-1`) is `coeff_tateOriginY_of_lt` and `coeff_tateOriginY_neg_three`; that
`(tateOriginX K, tateOriginY K)` satisfies the Weierstrass equation of the Tate curve is not
formalized.
