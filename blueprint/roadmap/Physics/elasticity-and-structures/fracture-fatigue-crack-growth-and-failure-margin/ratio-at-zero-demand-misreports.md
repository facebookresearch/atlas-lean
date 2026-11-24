# Ratio at zero demand misreports

The ratio formula must not be used at zero demand: Lean's `A / 0 = 0` makes `A / 0 - 1`
negative, a false failure signal, while the demand `0` does not fail.
