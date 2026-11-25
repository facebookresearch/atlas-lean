# On a passive line the energy grows by at most the net inflow

Let `R`, `L`, `G` and `C` be real per-unit-length constants, `U` an open subset of the `(x, t)`
plane, and `v`, `i` real functions of `(x, t)` that are continuously differentiable on `U` and
[solve the telegrapher equations](is-telegrapher-solution.md) on `U`, with `R ≥ 0` and `G ≥ 0`. Let
`ℓ > 0` and `t₀ ≤ t₁`, with the rectangle `[0, ℓ] × [t₀, t₁]` contained in `U`. Then the
[line energy](line-energy.md) `E(t) = ∫ from 0 to ℓ of u(x, t) dx` satisfies

`E(t₁) − E(t₀) ≤ ∫ from t₀ to t₁ of (S(0, s) − S(ℓ, s)) ds`,

with the [power flux](power-flux.md) `S = v i`: the stored energy grows by at most the net endpoint
inflow.
