# Total weight of the tangency direction in closed form

For every real square matrix `S` (a singular matrix being given the inverse `0`), expected returns
`μ` and risk-free return `r`, the tangency direction `z = S⁻¹ (μ - r 1)` has total weight
`1ᵀ z = 1ᵀ S⁻¹ μ - r · 1ᵀ S⁻¹ 1`. When `C = 1ᵀ S⁻¹ 1 ≠ 0` this is `C (μ_GMV - r)` with
`μ_GMV = (1ᵀ S⁻¹ μ) / C`, which for positive definite `S` is the expected return of the global
minimum-variance portfolio.
