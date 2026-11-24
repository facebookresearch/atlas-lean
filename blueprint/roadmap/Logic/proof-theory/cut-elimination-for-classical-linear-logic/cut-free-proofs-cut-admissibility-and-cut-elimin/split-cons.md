# Case split on an equation of cons sequents

Distinguish a principal selected occurrence using decidable equality.
Given `a ::ₘ Γ = b ::ₘ Δ`, either `a = b` and `Γ = Δ`, or `a ≠ b` and the propositions are swapped:
`Γ = b ::ₘ Λ` and `Δ = a ::ₘ Λ` for some `Λ`.
The tail `Δ` can be an arbitrary multiset; the residual list is obtained from `Γ`.
