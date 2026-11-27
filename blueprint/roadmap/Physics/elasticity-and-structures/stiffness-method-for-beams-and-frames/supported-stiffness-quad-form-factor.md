# Supported quadratic form of the two-span beam as sums of squares

For all real `EI1`, `L1`, `EI2`, `L2` and every `w = (w0, w1, w2)`, the
[supported stiffness](supported-stiffness.md) `K_s` satisfies `w · K_s w = Q₁ + Q₂` with
`Q₁ = (EI1 / L1 ^ 3) (12 ((L1 / 2) (w0 + w1))² + L1² (w0 - w1)²)` and
`Q₂ = (EI2 / L2 ^ 3) (12 ((L2 / 2) (w1 + w2))² + L2² (w1 - w2)²)`: only rotational squares remain
after the support injection. A span of length `0` contributes `0`, by the convention `x / 0 = 0`.
The physical reading is `EI1, L1, EI2, L2 > 0`.
