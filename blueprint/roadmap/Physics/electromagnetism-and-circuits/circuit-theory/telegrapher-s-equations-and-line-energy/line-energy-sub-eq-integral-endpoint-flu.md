# Integrated energy balance of a finite line

Let `R`, `L`, `G` and `C` be real per-unit-length constants, `U` an open subset of the `(x, t)`
plane, and `v`, `i` real functions of `(x, t)` that are continuously differentiable on `U` and
[solve the telegrapher equations](is-telegrapher-solution.md) on `U`. Let `ℓ > 0` and `t₀ ≤ t₁`,
with the rectangle `[0, ℓ] × [t₀, t₁]` contained in `U`. Then the [line energy](line-energy.md)
`E(t) = ∫ from 0 to ℓ of u(x, t) dx` satisfies

`E(t₁) − E(t₀) = ∫ from t₀ to t₁ of (S(0, s) − S(ℓ, s)) ds`
`− ∫ from t₀ to t₁ ∫ from 0 to ℓ of d(x, s) dx ds`,

with the [power flux](power-flux.md) `S = v i` and the [dissipation density](dissipation-density.md)
`d = R i² + G v²`: the energy change is the integrated inflow at `x = 0` minus the outflow at
`x = ℓ`, minus the integrated dissipation.
