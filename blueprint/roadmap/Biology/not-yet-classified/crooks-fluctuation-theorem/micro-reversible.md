# Micro Reversible

The setting of Crooks (1999): `bar` is an involution of the states; the initial densities
`ρ_F` and `ρ_R` are positive probability vectors; the transition matrices `M` (forward
protocol) and `MR` (time-reversed protocol) are stochastic; the heats `QF` (forward protocol)
and `QR` (time-reversed protocol) satisfy `QR[x̄(-t)] = -QF[x]` for every path `x`; and the
dynamics are microscopically reversible:
`∏_i M_i(x_i, x_{i+1}) = e^{-β QF[x]} ∏_i MR_i(x̄_{n-i}, x̄_{n-i-1})` for every path `x`.
