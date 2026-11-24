# Charging Sum

Charging transient `V t x = c cosh ((L - x)/ℓ) + ∑_{n ∈ s} a n e^{-k_n t} cos (n π x / L)`:
steady response to a constant injected current at `x = 0` plus a sealed-end expansion, which
decays when `τ > 0` (`tendsto_chargingSum`).
