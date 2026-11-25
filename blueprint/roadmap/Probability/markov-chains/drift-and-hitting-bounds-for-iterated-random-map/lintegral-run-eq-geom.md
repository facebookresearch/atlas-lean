# Lintegral run eq geom

Assume `Measurable (fun p : S × D => f p.1 p.2)`, `Measurable V` and `∀ x, ∫⁻ d, V (f x d) ∂law = ρ * V x + β`.

The drift recursion with equality: if one step satisfies
`E V(f x d) = ρ V(x) + β`, then the expectation of `V` at mark `n` is exactly
`ρⁿ V(x₀) + β ∑_{k<n} ρᵏ`.
