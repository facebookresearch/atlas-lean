# Strong consistency of the rate root with random size factors

On a probability space `(Ω, μ)`, let `(S₀, X₀), (S₁, X₁), …` be pairs of measurable random
variables, a size factor `Sᵢ` with `Sᵢ(ω) > 0` for every `ω` and a count `Xᵢ` with values in `ℕ`.
Assume the pairs are pairwise independent (`(Sᵢ, Xᵢ)` and `(Sⱼ, Xⱼ)` are independent for `i ≠ j`)
and identically distributed, and `X₀` is integrable. Let `a > 0` and `b₀ > 0` solve the population
rate equation `R(a, b₀) = 0`, where `R(a, b) = a - E[(a + X₀) b / (b + S₀)]` is the
[population rate score](pop-rate-score-log.md). Then, almost surely, for all large `n` the
[rate root](rate-root.md) `b̂ₙ(a)` of the first `n` cells (the counts `X₀(ω), …, X₍ₙ₋₁₎(ω)` at the
size factors `S₀(ω), …, S₍ₙ₋₁₎(ω)`) solves their
[rate score](../likelihood-equations-and-efficiency-of-the-gamma/rate-score.md) equation, and
`b̂ₙ(a) → b₀` as `n → ∞`.

The equation `R(a, b₀) = 0` holds, for example, when `E[X₀ ∣ S₀] = a S₀ / b₀` almost surely
([a matching conditional mean](pop-rate-score-log-eq-zero-of-cond-mean.md)).
