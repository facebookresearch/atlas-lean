# Consistent loads of a uniform load from Hermite shape functions

For `L ≠ 0` and every real `w`, the Hermite shape functions `h₁ = 1 - 3 ξ² + 2 ξ³`,
`h₂ = L (ξ - 2 ξ² + ξ³)`, `h₃ = 3 ξ² - 2 ξ³` and `h₄ = L (-ξ² + ξ³)` with `ξ = x / L`, in the nodal
order `(v1, θ1, v2, θ2)` (end-1 deflection, end-1 rotation, end-2 deflection, end-2 rotation), give
`∫_0^L w h₁ dx = w L / 2`, `∫_0^L w h₂ dx = w L² / 12`, `∫_0^L w h₃ dx = w L / 2` and
`∫_0^L w h₄ dx = -w L² / 12`: the two deflection entries sum to the total load `w L`, and the
rotation entries are opposite. The integrals are oriented; the physical reading is `L > 0`.
