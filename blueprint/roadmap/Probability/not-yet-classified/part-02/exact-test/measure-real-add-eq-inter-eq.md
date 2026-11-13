# Binomial conditioning, joint form

Let `X ~ Po(s₁ r)` and `Y ~ Po(s₂ r)` be independent
counts of one gene in two conditions with library sizes `s₁, s₂` (`s₁ + s₂ > 0`) and a common
rate `r ≥ 0`. Then for every total `n` and cell `k`,
`P(X + Y = n, X = k) = Bin(n, s₁ / (s₁ + s₂)){k} · P(X + Y = n)`. This needs no positivity of
`r` and no conditioning on a null event.
