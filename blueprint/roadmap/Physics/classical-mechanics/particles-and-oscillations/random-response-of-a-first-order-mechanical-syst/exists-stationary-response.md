# Existence of a pathwise stationary response

For `c, k > 0` and every `σ` there is a
probability space carrying a Brownian motion `B` and a start `X₀ ~ N(0, σ² / (2 c k))` independent
of `B` such that the OU path solution `X t ω = ouPathSolution (k / c) (σ / c) (X₀ ω) (B · ω) t`
solves the physical equation `c (x t - x₀) = -k ∫₀ᵗ x + σ (w t - w 0)` with `w = B · ω` along
almost every path, and is a stationary OU process with rate `k / c` and noise amplitude
`σ / c`.
