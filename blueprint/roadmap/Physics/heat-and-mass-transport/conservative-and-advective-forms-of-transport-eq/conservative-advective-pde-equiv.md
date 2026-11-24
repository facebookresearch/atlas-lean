# Where ∂U/∂x = 0, conservative and advective forms are equivalent

Let `U : ℝ → ℝ`, `c(t, x)` a concentration and `D`, `k`, `t`, `x` real. Suppose `U` has derivative
`0` at `x`, and `c(t, ·)` and its derivative `c_x(t, ·)` are differentiable at `x`. Then the
conservative form

`c_t + ∂/∂x (U c - D c_x) = -k c`

holds at `(t, x)` if and only if the advective form `c_t + U c_x - D c_xx = -k c` holds there. The
derivatives are total ones in one variable with the other held fixed; regularity is assumed only at
the point.
