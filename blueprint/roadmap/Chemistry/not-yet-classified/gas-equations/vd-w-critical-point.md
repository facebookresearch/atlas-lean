# Vd W critical point

Van der Waals model, critical point. If `a, b, R, T > 0`, `Vm > b`, and both critical
equations `∂p/∂V_m = 0` and `∂²p/∂V_m² = 0` hold at `(Vm, T)` (in the explicit forms given by
`hasDerivAt_vdWPressure` and `hasDerivAt_deriv_vdWPressure`), then the critical molar volume is
`Vm = 3 b`, the critical temperature is `T = 8 a / (27 R b)`, the critical pressure is
`a / (27 b ^ 2)` and the critical compressibility factor is `3 / 8`.

Below the critical temperature, for positive pressures between the local extrema of an isotherm,
the van der Waals cubic has three real roots `V_m > b`, the middle one on an unphysical branch;
the Maxwell construction is elective and is not included here.
