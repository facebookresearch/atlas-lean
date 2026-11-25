# Mass balance of the explicit amount

For all real `k`, `R` and `A₀` and every `t ≥ 0`, the amount
`A(t) = A₀ * exp (-k * t) + ∫₀ᵗ exp (-k * (t - s)) * R ds` of the one-compartment model with
elimination rate `k`, constant input `R` and initial amount `A₀`, which is
`R / k + (A₀ - R / k) * exp (-k * t)` for `k ≠ 0` and `A₀ + R * t` for `k = 0`, satisfies
`A(t) + ∫₀ᵗ k * A(s) ds = A₀ + R * t`.
