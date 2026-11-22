# Mean position in a box state is L/2

For `n ≥ 1` and `L > 0`, the square of the box state `ψ_n(x) = √(2/L) * sin (n * π * x / L)` is a
probability density on `[0, L]` (see [normalization](box-orthonormality-diag.md)), and the mean
position in the state is `⟨x⟩ = ∫₀ᴸ x * ψ_n(x)^2 dx = L / 2`. Indeed
`x * ψ_n(x)^2 = x / L - (x / L) * cos (2 * n * π * x / L)`, and the integral of
`x * cos (2 * n * π * x / L)` over `[0, L]` vanishes.
