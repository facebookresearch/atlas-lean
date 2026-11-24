# Charge conservation up to membrane leak

The total potential after a unit charge decays at
exactly the membrane rate: `∫₀ᴸ G(t, x; x₀) dx = e^{-t/τ}` for `t > 0`, wherever the input is.
For `L < 0` the integral is oriented, which compensates for the sign of the kernel
(`sealedGreen_neg_length`); the physical statement is the case `0 < L`, `x₀ ∈ [0, L]`.
