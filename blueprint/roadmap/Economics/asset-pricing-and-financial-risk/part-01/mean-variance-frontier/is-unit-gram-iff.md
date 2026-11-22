# Constraint Gram matrix is invertible iff not all means are equal

For a positive definite covariance matrix `S` and expected returns `μ`, the `2 × 2` Gram matrix
`Mᵀ S⁻¹ M` of the constraint matrix `M = [1 μ]` is invertible iff the budget and mean
constraints are independent, i.e. the mean vector `μ` is not constant (not proportional to the
vector of ones): `μ_i ≠ μ_j` for some assets `i` and `j`.
