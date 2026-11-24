# Parabolic solution nonneg

Nonnegativity for a classical scalar parabolic solution: let
`c` solve `c_t - D * c_xx + k * c = s` on the closed cylinder
`[0, T] × [0, L]` in the sense that its time derivative `ct`,
first and second spatial derivatives `cx`, `cxx` are given
functions related by the displayed `HasDerivAt` data, with
`D > 0`, `k ≥ 0`, `s ≥ 0` pointwise on the cylinder, nonnegative
initial data `c 0 x ≥ 0` on `[0, L]`, and nonnegative Dirichlet
data `c t 0 ≥ 0`, `c t L ≥ 0` on `[0, T]`. Then `c t x ≥ 0` on the
whole cylinder. This is a comparison theorem for a given
classical solution, not an existence claim. The proof is the
compact negative-minimum argument applied to
`c + ε * (t + 1)`, then `ε → 0`.
