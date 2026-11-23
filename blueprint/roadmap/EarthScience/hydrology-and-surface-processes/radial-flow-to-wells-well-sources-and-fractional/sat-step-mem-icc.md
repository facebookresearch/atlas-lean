# The saturation step keeps saturations in the mobile range

For viscosities `μo > 0` and `μw > 0`, `ΔS = 1 - Sor - Swc > 0`, a positive pore volume
`φ * A * dx > 0`, `Q ≥ 0` and `dt ≥ 0`, let the [CFL number](cfl-number.md)
`ν = Q * dt / (φ * A * dx * ΔS)` satisfy `ν * B ≤ 1`, where `B = (μo + μw) ^ 2 / (2 * μo * μw)`.
Then a [physical step](sat-step.md) from saturations in the mobile range `[Swc, 1 - Sor]`, with an
inflow saturation in that range, gives saturations in `[Swc, 1 - Sor]`.
