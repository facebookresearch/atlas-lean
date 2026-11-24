# Advection diffusion nondimensional

Nondimensionalization of the advection-diffusion equation: with
`x = L * x̂`, `t = (L / U) * t̂`, `c = C0 * ĉ`, the chain rule gives
`c_t = C0 * (U / L) * ĉ_t̂`, `c_x = (C0 / L) * ĉ_x̂`,
`c_xx = (C0 / L ^ 2) * ĉ_x̂x̂` (as derivative values at corresponding
points). If `c` satisfies `c_t + U * c_x = D * c_xx`, then the scaled
derivatives satisfy `ĉ_t̂ + ĉ_x̂ = (1 / Pe) * ĉ_x̂x̂` with
`Pe = U * L / D`.
