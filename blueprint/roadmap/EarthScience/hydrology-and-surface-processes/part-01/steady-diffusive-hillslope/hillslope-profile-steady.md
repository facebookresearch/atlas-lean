# The parabolic hillslope profile is steady under diffusion with uplift

For a diffusivity `D > 0`, a half-width `L > 0` and an uplift rate `U ≥ 0`, the profile
`z(x) = U * (L ^ 2 - x ^ 2) / (2 * D)` has second derivative `z''(x) = -U / D` at every real `x`,
so `U + D * z''(x) = 0`: it is a steady state of the linear diffusive hillslope model
`z_t = U + D * z_xx`.
