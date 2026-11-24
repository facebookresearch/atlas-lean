# The consistent load vector entries as Hermite integrals

For `L ≠ 0` and every real `w`, the four entries of the
[consistent load vector](uniform-load-vector.md) are the integrals `∫_0^L w h_i(x) dx` of the
Hermite shape functions with unit end data, in the order `(v1, θ1, v2, θ2)`: `h₁ = 1 - 3 ξ² + 2 ξ³`,
`h₂ = L (ξ - 2 ξ² + ξ³)`, `h₃ = 3 ξ² - 2 ξ³` and `h₄ = L (-ξ² + ξ³)` with `ξ = x / L`, where `h_i`
is the Hermite cubic on `[0, L]` whose `i`-th end datum is `1` and the others `0`.
