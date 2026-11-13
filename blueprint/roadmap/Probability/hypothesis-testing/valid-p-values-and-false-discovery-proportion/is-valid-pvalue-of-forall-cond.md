# Validity from conditional validity

Let `S` be a measurable count that is at most `N`
almost surely, and let `P` agree with `q (S ω)` wherever `S ω ≤ N`. If each `q t` is a valid
p-value conditionally on `S = t` (for `t ≤ N`), then `P` is valid under `μ`.

This is the law of total probability: `μ {P ≤ s} ≤ ∑ₜ μ {S = t} μ[P ≤ s | S = t] ≤ s`.
