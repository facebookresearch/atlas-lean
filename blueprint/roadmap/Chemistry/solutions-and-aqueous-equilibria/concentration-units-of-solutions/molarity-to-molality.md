# Conversion from molarity to molality

Molarity-to-molality conversion `b = c / (ρ - c * M)` for solution density `ρ` and solute
molar mass `M`, meant for the physical domain `0 ≤ c ∧ c < ρ / M`, which it maps bijectively
onto `b ≥ 0` for positive `ρ` and `M` ([the conversion bijection](bij-on-molarity-to-molality.md)).
It is defined for all real `ρ`, `M` and `c`: where `ρ - c * M = 0` the convention `x / 0 = 0`
makes it `0`; on the physical domain the denominator is positive.
