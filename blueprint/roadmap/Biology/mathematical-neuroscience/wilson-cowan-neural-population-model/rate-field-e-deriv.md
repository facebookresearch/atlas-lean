# Partial derivatives of the excitatory Wilson–Cowan field

Let `τ_E`, `r_E`, `h_E`, `w_EE`, `w_EI`, `x`, `y` be real, and let the gain `f_E : ℝ → ℝ` have
derivative `f_E'` at the input `s = h_E - w_EI y + w_EE x`. The excitatory component of the
Wilson–Cowan field with refractory factor,

`E(x, y) = (-x + (1 - r_E x) f_E(h_E - w_EI y + w_EE x)) / τ_E`,

has at `(x, y)` the partial derivatives

`∂E/∂x = (-1 - r_E f_E(s) + (1 - r_E x) f_E' w_EE) / τ_E` and
`∂E/∂y = (1 - r_E x) f_E' (-w_EI) / τ_E`.

The term `-r_E f_E(s)` comes from differentiating the refractory factor `1 - r_E x`; at `r_E = 0`
the formulas are those of the field without refractory factor. In the model the time constants are
positive and the refractory coefficients nonnegative; the identities hold for all real values, a
zero time constant included, where both sides are `0` by the convention `q / 0 = 0`.
