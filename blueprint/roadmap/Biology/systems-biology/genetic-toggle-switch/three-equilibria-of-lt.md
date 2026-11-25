# For a, b > 0, three roots: two linearly stable equilibria and a saddle

For `a > 0` and `b > 0` and real roots `r < s < t` of the [equilibrium cubic](cubic.md)
`c(u) = u³ − a u² + (1 + b) u − a`, the [set of equilibria](equilibria.md) of the toggle switch with
Hill exponents `β = 1`, `γ = 2` and rates `a = α₁`, `b = α₂` is `{(r, v_r), (s, v_s), (t, v_t)}`
with `v_x = b / (1 + x²)`, and `v_t < v_s < v_r`. The [Jacobian matrix](jacobian.md) is
[Hurwitz](../../../LinearAlgebra/special-matrices/m-matrices-and-hurwitz-stability/nonsingular-m-matrices/is-hurwitz.md)
(every eigenvalue has negative real part) at `(r, v_r)` and at `(t, v_t)`, and has
[saddle spectrum](has-saddle-spectrum.md) at `(s, v_s)`.
