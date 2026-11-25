# Taylor's theorem with Cauchy integral remainder

Taylor's theorem for analytic functions, with the Cauchy integral form of the remainder.

If `f` is analytic on an open set `Ω` containing `a`, then for every `n` there is a function `fₙ`,
analytic on `Ω`, such that
`f z = ∑ k < n, f⁽ᵏ⁾(a) / k! * (z - a) ^ k + fₙ z * (z - a) ^ n` for `z ∈ Ω`, and, whenever the
closed disc of radius `r` about `a` lies in `Ω`, for every `z` inside the circle `C(a, r)`
`fₙ z = (2πi)⁻¹ ∮_{C(a, r)} f ζ / ((ζ - a) ^ n * (ζ - z)) dζ`.
