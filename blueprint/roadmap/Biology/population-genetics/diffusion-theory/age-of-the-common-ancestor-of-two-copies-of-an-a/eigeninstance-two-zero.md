# Eigen-instance of Theorem 1, `k = 2`, `n = 0`

With `w₀ = 1` (Table A1) and
eigenvalue `λ = 3`, `β(x) = x² (1 - x)` satisfies Appendix Equation A1,
`(1 - 3x) β(x) = x² (1 - x) / 2 * β''(x)`. The separated solution of Patterson's
Equation 4 is then `e^{-3t} β(x)`; the general spectral statement needs Jacobi
polynomial theory absent from Mathlib and is not formalized here.
