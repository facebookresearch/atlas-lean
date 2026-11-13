# Sis Infected

The **explicit SIS solution** for the infectives with initial value `I₀`:
`I(t) = I₀ e^{r t} / (1 + (β I₀ / N) φ_r(t))`, `r = β - γ`, `φ_r = growthIntegral r`.
For `r ≠ 0` this is `I₀ e^{r t} / (1 + (β I₀ / (N r)) (e^{r t} - 1))`; for `β = γ` it is
`I₀ / (1 + β I₀ t / N)`; for `β = 0` it is `I₀ e^{-γ t}`; for `I₀ = 0` it is `0`.
