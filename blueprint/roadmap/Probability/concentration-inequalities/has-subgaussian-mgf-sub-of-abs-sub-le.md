# Sub-Gaussian bound for martingales with bounded increments

Let `Z₀, Z₁, …` be a real
martingale with respect to a filtration on a probability space, let `n` be a natural number and
suppose `|Zᵢ - Zᵢ₋₁| ≤ cᵢ` almost everywhere for `1 ≤ i ≤ n`. Then `Zₙ - Z₀` has a sub-Gaussian
moment-generating function with parameter `∑_{i=1}^n cᵢ²`: for every real `t`,
`exp (t (Zₙ - Z₀))` is integrable and `E[exp (t (Zₙ - Z₀))] ≤ exp ((∑_{i=1}^n cᵢ²) t² / 2)`.
