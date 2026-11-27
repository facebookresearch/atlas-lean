# Physical upwind step of the water saturations

On a chain of `n + 1` cells of length `dx`, cross-section `A` and porosity `φ`, at total
volumetric rate `Q` and time step `dt`, with water saturations `S 0, …, S n` and inflow
saturation `S_in`, one physical step replaces `S i` by
`S i - Q * dt / (φ * A * dx) * (f(s i) - f(s (i - 1)))`, where `s i` is the
[normalized saturation](norm-sat.md) of `S i`, `s (-1)` that of `S_in`, and `f` the
[fractional flow](frac-flow.md): the water volume of cell `i` changes by
`Q * dt * (f(s (i - 1)) - f(s i))` over the pore volume `φ * A * dx`. It is defined for all real
arguments: with the convention `x / 0 = 0` the saturations are unchanged when `φ * A * dx = 0`,
and also when `ΔS = 0`, since every normalized saturation is then `0` and the face flows are
equal. The intended domain is a positive pore volume `φ * A * dx > 0` and
`ΔS = 1 - Sor - Swc > 0`.
