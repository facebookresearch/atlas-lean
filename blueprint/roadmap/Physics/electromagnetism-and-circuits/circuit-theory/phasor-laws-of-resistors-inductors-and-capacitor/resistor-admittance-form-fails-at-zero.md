# Resistor admittance form fails at zero

At `R = 0` the admittance form is not equivalent to the multiplicative equation
(`V / 0 = 0` in Lean), so the nonzero-denominator guard is necessary.
