# Siegert formula

**Siegert formula** (Siegert 1951). Let `P` be a probability measure, `τ > 0`, `σ > 0`,
`V₀ < θ`, and let `X` be an Ornstein–Uhlenbeck process started at `0` with rate `1/τ` and noise
amplitude `σ / √τ` under `P`, every path of which is continuous. Then the firing time of
`V(t) = μ + (V₀ - μ) e^{-t/τ} + X(t)` at threshold `θ` (with values in `WithTop ℝ≥0`) is finite
almost surely, its finite value `firingTimeValue` is integrable, and its mean is
`τ √π ∫_{(V₀-μ)/σ}^{(θ-μ)/σ} e^{u²} (1 + erf u) du`.

## Sources

- A. J. F. Siegert, "On the first passage time probability problem", Phys. Rev. 81 (1951) 617–623; "Mean time-to-fire for the noisy LIF neuron: a detailed derivation of the Siegert formula", arXiv:1501.04032.
