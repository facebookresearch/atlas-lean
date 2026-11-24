# Remaining mass fractions of burns at one exhaust speed multiply

Let `fuel : ℝ → ℝ → ℝ` be a supplied consumed-fraction functional (`fuel ve Δv` is the fraction of a
burn's initial mass consumed by a burn of delta-v `Δv` at the exhaust speed `ve`), and fix a real
`ve` with `fuel ve 0 = 0` and `(1 − fuel ve d₁)(1 − fuel ve d₂) = 1 − fuel ve (d₁ + d₂)` for all
real `d₁`, `d₂`. Then for every sequence `d : ℕ → ℝ` of signed delta-v and every `n ∈ ℕ`,
`∏_{k < n} (1 − fuel ve (d k)) = 1 − fuel ve (∑_{k < n} d k)`.
