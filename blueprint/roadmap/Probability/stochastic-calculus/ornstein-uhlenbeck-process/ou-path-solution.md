# Pathwise solution of the Langevin equation

The explicit solution of the pathwise Langevin equation driven by a path `w`:
`e^{-θt} x₀ + σ (w t - e^{-θt} w 0 - θ ∫_0^t e^{-θ(t-u)} w u du)`. This is
`e^{-θt} x₀ + σ ∫_0^t e^{-θ(t-u)} dw(u)` after integration by parts (the Itô-integral form for a
Brownian path is a wanted statement).
