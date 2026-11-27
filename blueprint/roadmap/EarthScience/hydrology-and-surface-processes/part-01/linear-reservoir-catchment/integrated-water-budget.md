# Integrated water budget of a linear reservoir

For a recession coefficient `k > 0`, any real inflow `I` and initial storage `S0`, and every real
time `t`, the storage `S(u) = I / k + (S0 - I / k) * exp (-k * u)` has the time integral
`∫₀ᵗ S(u) du = I * t / k + (S0 - I / k) * (1 - exp (-k * t)) / k`, and the storage change closes
the budget `S(t) - S0 = I * t - k * ∫₀ᵗ S(u) du`. For `t < 0` the integral is oriented:
`∫₀ᵗ = -∫ₜ⁰`.
