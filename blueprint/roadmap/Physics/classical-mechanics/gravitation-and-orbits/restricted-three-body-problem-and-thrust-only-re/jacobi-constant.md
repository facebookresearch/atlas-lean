# Jacobi function of a rotating-frame state

For reals `μ`, `x`, `y`, `vx` and `vy`, the Jacobi function of the rotating-frame state with
position `(x, y)` and velocity `(vx, vy)` is `C = 2 Ω(x, y) - (vx² + vy²)`, with `Ω` the
[effective potential](effective-potential.md). The intended domain is off both primaries; at a
primary `C` uses the finite value that the convention `u / 0 = 0` gives `Ω` there, so
`C = μ² + 2 μ - (vx² + vy²)` at the first primary `(-μ, 0)` and
`C = (1 - μ)² + 2 (1 - μ) - (vx² + vy²)` at the second, `(1 - μ, 0)`. It is constant on every
closed time interval on which a twice continuously differentiable path avoids both primaries and
obeys the unforced rotating equations
([Jacobi integral](jacobi-constant-eq-of-rotating-equations.md)). In the physical reading
`0 < μ < 1`.
