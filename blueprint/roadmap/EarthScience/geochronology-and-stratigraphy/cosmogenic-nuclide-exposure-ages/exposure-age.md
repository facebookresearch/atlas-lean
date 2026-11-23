# Exposure age from a nuclide inventory

The exposure age of an inventory `N`, for production rate `P` and decay constant `λ`:
`-log (1 - λ * N / P) / λ`. On the intended domain `P > 0`, `λ > 0` and `0 ≤ N < P / λ` it
inverts the inventory with no inherited nuclides, `t ↦ (P / λ) * (1 - exp (-λ * t))`. It is
defined for all real `P`, `λ` and `N`, with the conventions `x / 0 = 0`, `log 0 = 0` and
`log x = log |x|`: the age is `0` when `P = 0`, when `λ = 0` or when `λ * N = P`, and it is
`-log (λ * N / P - 1) / λ` when `λ * N / P > 1`.
