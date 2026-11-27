# Integral of a bounded function against a probability mass function

Let `S` be a finite set, `p : ℕ^S → ℝ` a probability mass function (`p(x) ≥ 0` for every `x` and
`∑_x p(x) = 1`), and `f : ℕ^S → ℝ` a function with `|f(x)| ≤ B` for every `x`. Then the integral
of `f` against the [measure with mass function `p`](count-law.md) is the weighted sum

`∫ f dμ_p = ∑_{x ∈ ℕ^S} p(x) f(x)`,

an absolutely convergent series.
