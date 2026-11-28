# A constant is a solution exactly when elimination balances infusion

For all real `Vmax`, `Km`, `R` and `c`, the constant function `c` solves the
[saturable-elimination equation](is-solution.md) `C'(t) = R - Vmax * C(t) / (Km + C(t))` at every
time `t ≥ 0` if and only if `Vmax * c / (Km + c) = R`. At `c = -Km` the elimination rate is `0` by
the convention `x / 0 = 0`, so that constant is a solution exactly when `R = 0`.
