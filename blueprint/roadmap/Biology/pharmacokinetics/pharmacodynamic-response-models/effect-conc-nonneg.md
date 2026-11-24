# Nonnegative input and initial effect keep the effect nonnegative

For a lag rate `ke0 > 0`, an initial effect `Ce0 ≥ 0`, a time `t ≥ 0` and a plasma concentration
with `Cp(s) ≥ 0` for every `s` in `[0, t]`, the [effect-compartment concentration](effect-conc.md)
`Ce(t) = Ce0 * exp (-ke0 * t) + ∫₀ᵗ exp (-ke0 * (t - s)) * (ke0 * Cp(s)) ds` is nonnegative. No
integrability of `Cp` is assumed: where the integrand is not integrable the integral is `0` by
convention, and `Ce(t) = Ce0 * exp (-ke0 * t) ≥ 0`.
