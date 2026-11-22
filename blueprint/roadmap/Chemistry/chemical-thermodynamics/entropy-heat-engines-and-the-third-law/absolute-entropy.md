# Absolute Entropy

The absolute molar entropy
`S(T) = ∫ t in 0..T, Cp t / t + ∑ k ∈ trans with Tt k ≤ T, ΔH k / Tt k` for molar heat
capacity `Cp : ℝ → ℝ`, finitely many first-order transitions (`trans`, with temperatures
`Tt k > 0` and molar enthalpies `ΔH k`), at absolute temperature `T ≥ 0`. The third-law
convention `S(0) = 0` for a perfect crystal is built in (integral from `0`).

Domain: the value is an entropy only when the entropy integral converges, that is under
`IntervalIntegrable (fun t => Cp t / t) MeasureTheory.volume 0 T`. Otherwise Mathlib's
interval integral takes its junk value `0` (`intervalIntegral.integral_undef`) and the
definition returns just the transition sum, which is NOT an entropy: `Cp = 1`, `T = 1` and no
transitions give `0` although `∫₀¹ dt / t` diverges. The lemmas that read `absoluteEntropy` as
an entropy assume this integrability (`hasDerivAt_absoluteEntropy`, `absoluteEntropy_mono`);
`absoluteEntropy_zero` needs none because the interval `0..0` is degenerate, and
`absoluteEntropy_insert_of_lt` is an identity of the transition sum. Likewise a transition at
`Tt k = 0` would contribute Lean's junk `ΔH k / 0 = 0`; the lemmas that use transition values
assume `0 < Tt k`. Debye remark (EF = empirical fit): the low-`T` Debye `T³` extrapolation
`Cp t ≈ a * t^3` makes `Cp t / t ≈ a * t^2` integrable at `0`; Debye's law itself is NOT
proved here.
