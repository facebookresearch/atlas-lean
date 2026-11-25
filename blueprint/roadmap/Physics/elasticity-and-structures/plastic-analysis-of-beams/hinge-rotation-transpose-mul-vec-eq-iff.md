# The equilibrium equation is the fixed-ended beam statics

For a span `L > 0`, every vector `σ = (σ₀, σ₁, σ₂)` of moments at the left end, mid-span and right
end, and every load intensity `w`, the equilibrium equation `Bᵀ σ = w f`, that is
`(-2 σ₀ + 4 σ₁ - 2 σ₂) / L = w * L / 2` with the [hinge-rotation matrix](hinge-rotation.md)
`B = (-2 / L, 4 / L, -2 / L)ᵀ` (a 3 × 1 matrix: rows the critical sections at the left end, mid-span
and right end; column the central deflection) and the [work vector](uniform-load-work.md)
`f = (L / 2)` holds if and only if `σ₁ - (σ₀ + σ₂) / 2 = w * L ^ 2 / 8`: the mid-span moment minus
the mean end moment equals `w * L ^ 2 / 8` (Neal, equation (2.2), `M₂ - M₁ = W l / 8`, written there
for equal end moments).
