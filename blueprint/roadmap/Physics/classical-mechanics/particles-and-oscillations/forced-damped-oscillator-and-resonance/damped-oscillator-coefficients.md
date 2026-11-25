# Steady-state coefficients of the forced damped oscillator

Let `F`, `γ`, `ω₀` and `ω` be real numbers with `D = (ω₀² - ω²)² + (2 γ ω)² ≠ 0`, and let

`A = F (ω₀² - ω²) / D` and `B = F (2 γ ω) / D`.

Then `A` and `B` solve the two coefficient equations

`(ω₀² - ω²) A + 2 γ ω B = F` and `(ω₀² - ω²) B - 2 γ ω A = 0`,

which make `A cos (ω t) + B sin (ω t)` a solution of `x'' + 2 γ x' + ω₀² x = F cos (ω t)`
([equation](damped-oscillator-ode.md)). The condition `D ≠ 0` fails exactly when `ω² = ω₀²` and
`γ ω = 0`, for example at undamped resonance.
