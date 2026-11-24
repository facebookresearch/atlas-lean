# Quadratic form of the beam element stiffness matrix

For all real `EI` and `L` and all end data `d = (v1, θ1, v2, θ2)`, the
[beam stiffness matrix](beam-stiffness.md) `K` satisfies
`d · K d = (EI / L ^ 3) (12 (v1 - v2)² + 12 L (v1 - v2) (θ1 + θ2) + 4 L² (θ1² + θ1 θ2 + θ2²))`,
twice the strain energy in the physical reading. At `L = 0` both sides are `0`, by the convention
`x / 0 = 0`. The physical reading is `EI > 0` and `L > 0`.
