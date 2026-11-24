# Steady-state coefficients in the forced-oscillator convention

Let `m > 0` and `k ≥ 0`, and let `c`, `F` and `Ω` be real numbers. With the
[damping rate](atlas-damping.md) `γ = c / (2 m)`, the
[natural angular frequency](atlas-natural-frequency.md) `ω₀ = √(k / m)` and the
[forcing amplitude](atlas-forcing.md) `f = F / m`, the [in-phase coefficient](steady-state-cos.md)
`A` and the [quadrature coefficient](steady-state-sin.md) `B` of the steady-state response are

`A = f (ω₀² - Ω²) / D'` and `B = f (2 γ Ω) / D'`, where `D' = (ω₀² - Ω²)² + (2 γ Ω)²`.

These are the coefficients of the forced-oscillator convention
`x'' + 2 γ x' + ω₀² x = f cos (Ω t)`. No nonvanishing condition is needed: `D'` vanishes together
with the steady-state denominator, and with the convention `u / 0 = 0` both sides are then `0`.
