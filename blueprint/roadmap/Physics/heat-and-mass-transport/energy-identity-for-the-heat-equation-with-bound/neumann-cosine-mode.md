# Neumann Cosine Mode

Neumann cosine mode (nonzero boundary fixture, `h0 = hL = 0`). With
`μ = π / L`, `u t x = Ta + exp (-D * μ^2 * t) * cos (μ * x)` has zero flux
at both ends and `θ(t, 0) ≠ 0`. This fixture records only the first
spatial derivative and the zero-flux boundary conditions; the
heat-equation content for cosine modes is in `robinCosineMode`.
