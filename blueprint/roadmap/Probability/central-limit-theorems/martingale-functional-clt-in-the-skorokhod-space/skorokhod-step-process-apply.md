# Skorokhod Step Process apply

Explicit partial-sum formula: `(∑_{i < ⌊n t⌋} X i ω) / √n`.

In symbols: `skorokhodStepProcess n X ω t = (∑ i ∈ Finset.range (Nat.floor ((n : ℝ) * t.1)), X i ω) / Real.sqrt n`.
