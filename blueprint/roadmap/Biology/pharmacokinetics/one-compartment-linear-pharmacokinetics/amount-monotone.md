# Starting at or below the steady state the amount is nondecreasing

For `k > 0`, a real input `R` and an initial amount `A₀ ≤ R / k`, the amount
`A(t) = A₀ * exp (-k * t) + ∫₀ᵗ exp (-k * (t - s)) * R ds` of the one-compartment model with
elimination rate `k`, constant input `R` and initial amount `A₀`, which is
`R / k + (A₀ - R / k) * exp (-k * t)` for `k ≠ 0` and `A₀ + R * t` for `k = 0`, is nondecreasing in
`t` on the whole real line; it is constant when `A₀ = R / k`.
