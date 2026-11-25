# Effect-compartment concentration

For a lag rate `ke0`, a plasma concentration `Cp` (a function of time) and an initial effect
concentration `Ce0`, the effect-compartment concentration at time `t` is the relaxation solution
`Ce(t) = Ce0 * exp (-ke0 * t) + ∫₀ᵗ exp (-ke0 * (t - s)) * (ke0 * Cp(s)) ds`. It is defined for all
real `ke0`, `Ce0` and `t` and every function `Cp`: for `t < 0` the integral is oriented,
`∫₀ᵗ = -∫ₜ⁰`, and it is `0` when the integrand is not integrable on the interval. The intended
domain is `ke0 > 0`, `Ce0 ≥ 0`, `Cp ≥ 0` and `t ≥ 0`. If `Cp` is integrable on every bounded
interval, `Ce` solves the [lag equation](has-deriv-at-effect-conc.md) `Ce' = ke0 * (Cp - Ce)` at
every time where `Cp` is continuous.
