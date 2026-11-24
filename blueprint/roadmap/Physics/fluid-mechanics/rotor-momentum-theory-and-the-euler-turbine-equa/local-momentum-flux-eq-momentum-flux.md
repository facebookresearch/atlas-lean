# The local momentum flux is A times the momentum flux with stress −p 1

For a [port](rotor-port.md) with density `ρ`, area `A`, pressure `p`,
[inertial velocity](velocity.md) `c` and [outward unit normal](normal.md) `n`, and for every point
`x` of `ℝ³`, the [area-weighted local momentum flux](local-momentum-flux.md) `ṁ c + p A n` is `A`
times the momentum flux through `n` of the constant fields `ρ`, `c` and the pressure-only stress
`σ = -p 1`, evaluated at `x`. The momentum flux of `j`-momentum across a face normal to `e_i` is
`ρ c_j c_i - σ_ji`, convective transport minus the surface force, here `ρ c_j c_i + p δ_ji`; so the
`j`-th inertial component is `ṁ c_j + p A n_j = A Σ_i (ρ c_j c_i + p δ_ji) n_i`. As the fields are
constant, the point `x` does not enter.
