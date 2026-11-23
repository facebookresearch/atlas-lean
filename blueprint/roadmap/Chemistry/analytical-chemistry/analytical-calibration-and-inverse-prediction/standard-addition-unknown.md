# Unknown concentration by standard addition

Standard-addition unknown from a fitted line: given the fitted intercept and
slope of the response-versus-added-concentration line, the unknown concentration is
`intercept / slope`. Parametrization: `intercept` and `slope` are the fitted line's
coefficients, and the sign convention is that the line `y = a + b * t` meets `y = 0` at
`t = -a / b`, so the unknown is `-t* = a / b` (positive for same-sign `a, b`). It is defined for
every slope: for `b = 0` the convention `x / 0 = 0` makes it `0`, while the line meets `y = 0`
in exactly one point only when `b ≠ 0`.
