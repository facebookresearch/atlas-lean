# Robin Cosine Mode

Robin cosine mode (nonzero fixture). `u t x = Ta + exp (-D * μ^2 * t) *
cos (μ * (x - L / 2))` with `ux` its `x`-derivative solves `u_t = D * u_xx` at
every point, satisfies the outward Robin conditions at both ends with
`h = k * μ * tan (μ * L / 2)`, has `h ≥ 0` when `0 ≤ μ`, `0 ≤ L` and
`μ * L / 2 < π / 2`, and has `θ(t, 0) ≠ 0` there.
