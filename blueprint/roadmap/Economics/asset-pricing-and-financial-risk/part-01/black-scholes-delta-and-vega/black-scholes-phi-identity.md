# Black–Scholes density identity S0 φ(d₁) = K e⁻ʳᵀ φ(d₂)

For `S0, K, σ, T > 0` and any real `r`, the standard normal density `φ` satisfies
`S0 φ(d₁) = K e^{-rT} φ(d₂)`, where `d₁ = (log (S0 / K) + (r + σ²/2) T) / (σ √T)` and
`d₂ = d₁ - σ √T`. It follows from `d₁² - d₂² = 2 log (S0 / K) + 2 r T` and the explicit density
`φ(x) = e^{-x²/2} / √(2π)`.
