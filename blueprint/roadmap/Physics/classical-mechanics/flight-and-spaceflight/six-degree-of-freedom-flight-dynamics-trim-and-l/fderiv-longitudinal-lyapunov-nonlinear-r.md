# Orbital derivative of the Lyapunov function along the nonlinear field

For every state `e = (x, z, θ, q) ∈ ℝ⁴`, with `‖e‖` the Euclidean norm, the derivative of the
[quadratic Lyapunov function](longitudinal-lyapunov.md) `V(e) = eᵀ P e` along the
[nonlinear reduced field](nonlinear-reduced-field.md) `f` is

`DV(e) f(e) = 2 f(e)ᵀ P e = −‖e‖² − x⁴ + (θ + q) (θ − sin θ)`:

the linear part gives `−‖e‖²` and the remainder `(−x³, 0, 0, θ − sin θ)` the other two terms.
