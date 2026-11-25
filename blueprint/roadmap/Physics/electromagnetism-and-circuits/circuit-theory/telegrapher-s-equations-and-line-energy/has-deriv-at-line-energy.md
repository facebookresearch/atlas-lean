# Rate of change of the energy stored on a line segment

Let `R`, `L`, `G` and `C` be real per-unit-length constants, `U` an open subset of the `(x, t)`
plane, and `v`, `i` real functions of `(x, t)` that are continuously differentiable on `U` and
[solve the telegrapher equations](is-telegrapher-solution.md) on `U`. Let `ℓ > 0` and `t` be real,
with the segment `[0, ℓ] × {t}` contained in `U`. Then the [line energy](line-energy.md)
`E(t) = ∫ from 0 to ℓ of u(x, t) dx` has at `t` the derivative

`E'(t) = S(0, t) − S(ℓ, t) − ∫ from 0 to ℓ of d(x, t) dx`,

with the [power flux](power-flux.md) `S = v i` and the [dissipation density](dissipation-density.md)
`d = R i² + G v²`: inflow at `x = 0`, outflow at `x = ℓ`, minus the dissipation.
