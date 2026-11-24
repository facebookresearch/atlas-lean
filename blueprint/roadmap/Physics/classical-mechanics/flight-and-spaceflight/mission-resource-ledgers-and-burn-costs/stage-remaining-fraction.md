# Remaining mass fraction of admissible staged burns

Let `fuel : ℝ → ℝ → ℝ` be a supplied consumed-fraction functional (`fuel ve Δv` is the fraction of a
burn's initial mass consumed by a burn of delta-v `Δv` at the exhaust speed `ve`), and fix a real
`ve` with `fuel ve 0 = 0` and `(1 − fuel ve d₁)(1 − fuel ve d₂) = 1 − fuel ve (d₁ + d₂)` for all
real `d₁`, `d₂`, with `ve > 0`, and suppose `1 − fuel ve (ve log(a / b)) = b / a` whenever
`0 < b ≤ a` (a burn from mass `a` to mass `b` consumes `1 − b / a`). Then for
[admissible stage masses](admissible-stage-masses.md) `m₀`, `m₁` of `n` burns,
`∏_{k < n} m₁ k / m₀ k = 1 − fuel ve (C)`, where `C = ∑_{k < n} ve log(m₀ k / m₁ k)` is the sum of
the [stage increments](stage-increment.md), each [nonnegative](stage-increment-nonneg.md);
jettisoned masses enter no factor. The hypothesis `ve > 0` restricts the statement to burn costs: at
a negative `ve` the premises can hold while every increment is negative.
