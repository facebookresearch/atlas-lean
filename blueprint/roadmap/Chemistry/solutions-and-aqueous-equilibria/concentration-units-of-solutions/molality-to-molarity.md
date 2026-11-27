# Conversion from molality to molarity

Molality-to-molarity conversion `c = b * ρ / (1 + b * M)` for solution density `ρ` and
solute molar mass `M`, meant for `b ≥ 0`, which it maps bijectively onto the physical molarity
domain for positive `ρ` and `M`
([the inverse conversion bijection](bij-on-molality-to-molarity.md)). It is defined for all real
`ρ`, `M` and `b`: where `1 + b * M = 0` the convention `x / 0 = 0` makes it `0`; for `b ≥ 0` and
`M > 0` the denominator is positive.
