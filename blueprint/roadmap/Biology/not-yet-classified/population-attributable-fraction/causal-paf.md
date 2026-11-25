# Causal PAF

The causal attributable fraction `1 - P(Y(0) = 1) / P(Y = 1)`, with
`P(Y(0) = 1) = ∑_z P(z) r₀(z)`: the net proportional change in population risk had the exposure been
absent (negative when the exposure is protective). It is meaningful when `P(Y = 1) > 0`; if
`P(Y = 1) = 0`, Lean's convention `x / 0 = 0` makes the quotient `0` and the value `1`.
