# The frame stiffness quadratic form as a sum of squares

For all real `EA`, `EI` and `L` and all `d = (u1, v1, θ1, u2, v2, θ2)`, the
[frame stiffness matrix](frame-stiffness.md) `K_f` satisfies
`d · K_f d = (EA / L) (u2 - u1)² + Q_b`, with the bending part
`Q_b = (EI / L ^ 3) (12 ((v1 - v2) + (L / 2) (θ1 + θ2))² + L² (θ1 - θ2)²)`; this is twice the strain
energy in the physical reading. At `L = 0` both sides are `0`, by the convention `x / 0 = 0`. The
physical reading is `EA > 0`, `EI > 0` and `L > 0`.
