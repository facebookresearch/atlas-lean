# Absorption

For `b, ε > 0`, with `C = absorbConst a b I` and `κ = decayRate b ε`,
`energy(t) ≤ e^{-2κt} energy(0) + (C / κ)(1 - e^{-2κt})` for `t ≥ 0`; in particular every
solution eventually enters every trapping ellipse (`C / κ = trapRadius`).

Proof: the dissipation inequality `energy' ≤ 2C - 2κ energy` and Mathlib's Grönwall bound
`le_gronwallBound_of_liminf_deriv_right_le` with `K = -2κ`.
