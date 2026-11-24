# Weak residual of the Burgers step from 2 to 0

For the Burgers flux `f(u) = u² / 2` and a smooth test function `φ` with time and space partial
derivatives `φ_t`, `φ_x` that vanishes outside a bounded rectangle, the
[weak residual](weak-residual.md) of the [moving step](moving-step.md) from `u_L = 2` to `u_R = 0`
is `0` at the speed `c = 1` and equals `2 ∫ φ(t, 0) dt` at the speed `c = 0`; the latter is nonzero
exactly when `∫ φ(t, 0) dt ≠ 0`.
