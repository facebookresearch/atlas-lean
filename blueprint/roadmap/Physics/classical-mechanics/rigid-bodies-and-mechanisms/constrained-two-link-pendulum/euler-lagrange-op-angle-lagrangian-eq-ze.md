# For positive masses and lengths, Euler–Lagrange is the reduced ODE

Let `m₁, m₂, l₁, l₂ > 0`, `g` real, and `q` a trajectory of angle vectors that is twice continuously
differentiable at `t`. Then the Euler–Lagrange operator `∂L/∂q - d/dt (∂L/∂v)` of the
[two-link Lagrangian](angle-lagrangian.md) along `q`, evaluated at `t`, vanishes if and only if
`q''(t)` is the [reduced acceleration](reduced-accel.md) at `(q(t), q'(t))`, that is,
`q''(t) = M(q(t))⁻¹ f(q(t), q'(t))` ([inverse form](reduced-accel-eq-inv-mul-vec.md)).
