# Tajima's `b₂` from Fu's closed form

`∑_{i,j=1}^{n-1} π_i π_j σ_{ij} = b₂ =
2 (n² + n + 3) / (9 n (n - 1))` with `π_i = i (n - i) / C(n, 2)` (Tajima 1983), so
`Var(θ_π[L]) = 4 b₂` and `Var θ_π = b₁ θ + b₂ θ²`. The `β_n` part cancels because the weights
are symmetric under `i ↦ n - i`.
