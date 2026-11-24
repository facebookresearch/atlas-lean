# The beam stiffness quadratic form as a sum of two squares

For all real `EI` and `L` and all end data `d = (v1, θ1, v2, θ2)`, the
[beam stiffness matrix](beam-stiffness.md) `K` satisfies
`d · K d = (EI / L ^ 3) (12 ((v1 - v2) + (L / 2) (θ1 + θ2))² + L² (θ1 - θ2)²)`. At `L = 0` both
sides are `0`, by the convention `x / 0 = 0`. The physical reading is `EI > 0` and `L > 0`.
