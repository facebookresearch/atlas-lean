# Mean square position in a box state

For `n ≥ 1` and `L > 0`, the square of the box state `ψ_n(x) = √(2/L) * sin (n * π * x / L)` is a
probability density on `[0, L]` (see [normalization](box-orthonormality-diag.md)), and the mean
square position in the state is `⟨x^2⟩ = ∫₀ᴸ x^2 * ψ_n(x)^2 dx = L^2 * (1/3 - 1/(2 * n^2 * π^2))`,
using `x^2 * ψ_n(x)^2 = x^2 / L - (x^2 / L) * cos (2 * n * π * x / L)`.
