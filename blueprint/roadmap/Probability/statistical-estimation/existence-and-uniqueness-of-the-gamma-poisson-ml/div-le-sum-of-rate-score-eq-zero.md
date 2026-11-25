# At a rate score root the fitted prior mean is at most ∑ᵢ kᵢ / sᵢ

For positive size factors `s₁, …, sₙ` (`n ≥ 1`), counts `k₁, …, kₙ`, a real `a` and `b > 0` solving
the [rate score](../../../Probability/statistical-estimation/likelihood-equations-and-efficiency-of-the-gamma/rate-score.md) equation
`∑ᵢ (a / b - (a + kᵢ) / (b + sᵢ)) = 0`, the fitted prior mean satisfies `a / b ≤ ∑ᵢ kᵢ / sᵢ`.
Otherwise every term `a / b - (a + kᵢ) / (b + sᵢ) = (a sᵢ - b kᵢ) / (b (b + sᵢ))` would be positive.
If some count is positive, this is the lower bound `b ≥ a / ∑ᵢ (kᵢ / sᵢ)`, for example for the
[rate root](rate-root.md) `b = b̂(a)` at `a > 0`.
