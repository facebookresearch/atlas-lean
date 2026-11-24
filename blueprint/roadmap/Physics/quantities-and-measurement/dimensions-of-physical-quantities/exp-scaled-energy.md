# Exp Scaled Energy

The Boltzmann/Arrhenius-style factor `exp (-(E / (R T)))` for a molar energy `E`, a gas
constant `R > 0` and an absolute temperature `T > 0`, each as a typed `WithDim` quantity.
The exponent is the `WithDim dimensionlessDim ℝ` quotient `E / (R * T)`: the dimension identity
`molarEnergyDim_div_gasConstantDim_mul_temperatureDim` is the cast that makes it
dimensionless, rather than a comment alongside unrelated raw reals.
