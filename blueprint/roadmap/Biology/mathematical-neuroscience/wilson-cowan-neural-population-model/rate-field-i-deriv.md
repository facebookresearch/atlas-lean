# Partial derivatives of the inhibitory Wilson–Cowan field

Let `τ_I`, `r_I`, `h_I`, `w_IE`, `w_II`, `x`, `y` be real, and let the gain `f_I : ℝ → ℝ` have
derivative `f_I'` at the input `s = h_I + w_IE x - w_II y`. The inhibitory component of the
Wilson–Cowan field with refractory factor,

`I(x, y) = (-y + (1 - r_I y) f_I(h_I + w_IE x - w_II y)) / τ_I`,

has at `(x, y)` the partial derivatives

`∂I/∂y = (-1 - r_I f_I(s) + (1 - r_I y) f_I' (-w_II)) / τ_I` and
`∂I/∂x = (1 - r_I y) f_I' w_IE / τ_I`.

The term `-r_I f_I(s)` comes from differentiating the refractory factor `1 - r_I y`. In the model
the time constants are positive and the refractory coefficients nonnegative; the identities hold for
all real values, a zero time constant included, where both sides are `0` by the convention
`q / 0 = 0`.
