# Minimum-variance portfolio for a target return

For finitely many assets with a real square matrix `S` (the covariance matrix), expected returns
`μ` and a target return `m`, the minimum-variance portfolio is `w* = Bᵀ (1, m)`, where
`B = (Mᵀ S⁻¹ M)⁻¹ Mᵀ S⁻¹` is the generalized least-squares matrix of the constraint matrix
`M = [1 μ]` and `S`. The formula is defined for every `S`, with the convention that the inverse
of a singular matrix is `0`.
