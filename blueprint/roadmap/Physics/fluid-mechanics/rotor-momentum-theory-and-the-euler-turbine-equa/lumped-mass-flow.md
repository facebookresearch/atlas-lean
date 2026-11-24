# Lumped mass flow ρ A (c · n) of a port

For a [port](rotor-port.md) with density `ρ ≥ 0`, area `A ≥ 0`, [inertial velocity](velocity.md) `c`
and [outward unit normal](normal.md) `n`, the lumped mass flow is `ṁ = ρ A (c · n)`: the local mass
flux `ρ (c · n)` through the outward normal at the representative point times the port area. As
`ρ A ≥ 0`, it is nonnegative for flow out of the control volume (`c · n ≥ 0`) and nonpositive for
flow into it (`c · n ≤ 0`). For `ρ A > 0` it has the sign of `c · n`, and it is `0` when `c · n = 0`
or `ρ A = 0`.
