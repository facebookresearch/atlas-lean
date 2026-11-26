# Ideal velocity increment of a burn

For a real `ve`, mass sequences `m₀, m₁ : ℕ → ℝ` and a burn `k`, `ve log(m₀ k / m₁ k)`, the ideal
velocity increment of a burn from the start mass `m₀ k` to the end mass `m₁ k` at the exhaust speed
`ve`. With the conventions `x / 0 = 0`, `log 0 = 0` and `log x = log |x|`, it is `0` when `m₀ k = 0`
or `m₁ k = 0`, and `ve log |m₀ k / m₁ k|` when the masses have opposite signs. It is meant for
[admissible stage masses](admissible-stage-masses.md).
