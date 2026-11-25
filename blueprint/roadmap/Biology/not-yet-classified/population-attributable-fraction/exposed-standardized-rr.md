# Exposed Standardized RR

The risk ratio standardized to the exposed, `∑_z P(z) e(z) r₁(z) / ∑_z P(z) e(z) r₀(z)`. It is
meaningful when `∑_z P(z) e(z) r₀(z) > 0`; a zero denominator gives `0` by Lean's convention
`x / 0 = 0`.
