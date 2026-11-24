# A test with nonzero front integral detects the jump condition

For a flux `f`, real numbers `u_L`, `u_R` and `c`, and a smooth test function `φ` with time and
space partial derivatives `φ_t`, `φ_x` that vanishes outside a bounded rectangle and satisfies
`∫ φ(t, c t) dt ≠ 0`, the [weak residual](weak-residual.md) of the [moving step](moving-step.md) is
`0` if and only if `c (u_R - u_L) = f(u_R) - f(u_L)`.
