# Choi Matrix

Repository-convention Choi matrix for an arbitrary complex-linear map
`Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ`.

The `((i,a),(j,b))` entry is `Φ (Matrix.single i j 1) a b`. Requires only
`[DecidableEq n]` for `Matrix.single`.
