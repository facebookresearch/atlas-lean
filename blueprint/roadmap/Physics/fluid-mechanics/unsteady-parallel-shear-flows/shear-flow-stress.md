# Newtonian stress of a parallel shear flow

If `U` is jointly twice continuously differentiable in `(t, y)`, then for all real `ρ`, `μ`, `λ`,
every pressure `p(t)`, time `t` and point `x` with `y = x₁`, the stress of the
[parallel shear flow](shear-flow.md) of constant density `ρ` with velocity `(U(t, y), 0, 0)`, `y`
the wall-normal coordinate is the matrix with rows `(-p(t), μ U_y, 0)`, `(μ U_y, -p(t), 0)` and
`(0, 0, -p(t))`, where `U_y` is the derivative of `U(t, ·)` at `y`: normal entries `-p(t)`, shear
entries `μ U_y`, and no contribution of the second viscosity.
