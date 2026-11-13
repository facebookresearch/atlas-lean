# Negative binomial mass function with size and mean

The negative binomial mass function with size `θ` and mean `μ`:
`NB(k; θ, μ) = θ⁽ᵏ⁾ / k! · (θ / (θ + μ)) ^ θ · (μ / (θ + μ)) ^ k`, with the rising factorial
`θ⁽ᵏ⁾ = Γ(θ + k) / Γ(θ)` and a real power `(θ / (θ + μ)) ^ θ`. The parameter domain is `θ > 0`,
`μ ≥ 0`; at `μ = 0` it is the point mass at `0`. Outside the domain the formula is not a
probability mass function.
