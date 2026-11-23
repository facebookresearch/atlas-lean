# Isothermal atmospheric pressure

Isothermal ideal-gas atmosphere: `p(z) = p0 * exp(-g * z / (R * T))`
with `p0, g, R, T > 0` satisfies the hydrostatic relation
`p'(z) = -(p(z) / (R * T)) * g` (density `rho = p / (R * T)`), has
`p(0) = p0`, stays positive, is strictly decreasing in `z`, and drops to
`p0 / exp 1` at one scale height `z = R * T / g`. The separate facts, with
their own hypotheses, are `hasDerivAt_isothermalPressure`,
`isothermalPressure_zero`, `isothermalPressure_pos`,
`isothermalPressure_strictAnti`, and `isothermalPressure_scaleHeight`.
