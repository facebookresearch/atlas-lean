# The pathwise Langevin solution driven by Brownian motion is Gaussian

For a Brownian
motion `B`, `θ ≠ 0`, any real `σ`, and a start `X₀ ~ N(0, v)` independent of `B`, the process
`X t = ouPathSolution θ σ X₀ B t` (`t ≥ 0`) is a Gaussian process with `E[X t] = 0` and
`cov[X s, X t] = e^{-θ(s+t)} (v + σ² (e^{2θ (s ∧ t)} - 1) / (2θ))` (Karatzas–Shreve 1991,
Section 5.6).
