# Absolute molar entropy with phase transitions

The absolute molar entropy `S(T) = ∫ t in 0..T, Cp t / t + ∑ k ∈ trans with Tt k ≤ T, ΔH k / Tt k`
for a molar heat capacity `Cp`, finitely many first-order transitions `k ∈ trans` (with temperatures
`Tt k > 0` and molar enthalpies `ΔH k`), at absolute temperature `T ≥ 0`. The third-law convention
`S(0) = 0` for a perfect crystal is built in (integral from `0`).

Domain: the value is an entropy only when `∫ t in 0..T, Cp t / t` converges. Otherwise the integral
is taken to be `0` and the value is just the transition sum, which is not an entropy: `Cp = 1`,
`T = 1` and no transitions give `0` although `∫₀¹ dt / t` diverges. Likewise a transition at
`Tt k = 0` contributes `ΔH k / 0 = 0`. Debye remark: the low-`T` Debye `T³` extrapolation
`Cp t ≈ a * t^3`, an empirical fit, makes `Cp t / t ≈ a * t^2` integrable at `0`; Debye's law itself
is not part of the statement.
