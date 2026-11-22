# Standard Addition Unknown

Standard-addition unknown from a fitted line (CH24.5a): given the fitted intercept and
slope of the response-versus-added-concentration line, the unknown concentration is
`intercept / slope`. The parametrization is fixed once here: `intercept` and `slope` are the
fitted line's coefficients, and the sign convention is that the line `y = a + b * t` meets
`y = 0` at `t = -a / b`, so the unknown is `-t* = a / b` (positive for same-sign `a, b`).
No Mathlib or ATLAS definition covers standard addition.
