# With no inherited nuclides the inventory at the exposure age of N is N

For a production rate `P > 0`, a decay constant `λ > 0` and an inventory `0 ≤ N < P / λ`, the
inventory with no inherited nuclides, `t ↦ (P / λ) * (1 - exp (-λ * t))`, evaluated at the
exposure age `t = -log (1 - λ * N / P) / λ` of `N`, returns `N`.
