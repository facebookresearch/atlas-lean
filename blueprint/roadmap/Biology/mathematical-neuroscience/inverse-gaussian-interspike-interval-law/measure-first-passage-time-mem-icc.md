# Gerstein–Mandelbrot interspike-interval law

**Gerstein–Mandelbrot interspike-interval law** (Gerstein and Mandelbrot 1964). Let `P` be a
probability measure, `B` a standard real Brownian motion under `P` (`IsBrownianReal B P`),
`z₀ > 0` the distance to threshold and `c ∈ ℝ` the drift towards it, and let the first passage
time of `c t + √2 B(t)` to `[z₀, ∞)` take values in `WithTop ℝ≥0` (`⊤` when the threshold is never
reached). Then for all `a, b : ℝ≥0` with `0 < a ≤ b`, the probability that the first passage time
lies in `[a, b]` equals `∫_a^b z₀ (4π)^{-1/2} T^{-3/2} exp(-(z₀ - cT)² / (4T)) dT`.

## Sources

- G. L. Gerstein and B. Mandelbrot, "Random walk models for the spike activity of a single neuron", Biophys. J. 4 (1964) 41–68.
