# Schweinsberg's formula for the block-count drift

For a finite measure `Λ` on `[0, 1]` and every natural number `b`, the
[block-count drift](block-drift.md) is
`γ_b = C(b, 2) Λ{0} + ∫_{(0,1]} (b x - 1 + (1 - x)^b) x⁻² Λ(dx)`: the Kingman atom at `0` is
split off, so the integrand is only evaluated at `x ≠ 0` and no division by zero occurs.
