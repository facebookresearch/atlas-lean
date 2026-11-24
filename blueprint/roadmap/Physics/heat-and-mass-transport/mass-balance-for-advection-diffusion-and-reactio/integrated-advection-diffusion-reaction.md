# Integrated advection–diffusion–reaction balance at one time

Let `c(t, x)` be a concentration and `U`, `D`, `k`, `a`, `b`, `t` real. Assume that at time `t`, at
every `x` between `a` and `b` (endpoints included, in either order): `c(t, ·)` has the derivative
`c_x(t, x)` at `x`, the map `x ↦ c_x(t, x)` has the derivative `c_xx(t, x)` at `x`, and

`c_t(t, x) + U c_x(t, x) = D c_xx(t, x) - k c(t, x)`,

where all derivatives are total ones in one variable with the other held fixed (`c_t` is `0` where
`c(·, x)` is not differentiable). Assume also that `c(t, ·)`, `c_x(t, ·)` and `c_xx(t, ·)` are
integrable between `a` and `b`. Write `J(t, x) = U c(t, x) - D c_x(t, x)` for the flux. Then

`∫_a^b c_t(t, x) dx = J(t, a) - J(t, b) - k ∫_a^b c(t, x) dx`.

The integrals are oriented: for `a ≤ b` the identity is the balance on `[a, b]`, net inflow minus
decay; for `b < a` both sides are the negatives of the balance on `[b, a]`. It holds for all real
`U`, `D` and `k`; the diffusion and decay reading needs `D ≥ 0`, `k ≥ 0` and `c ≥ 0`.
