# Canonical 2PL score

The `VectorInference.score` (parameter
space `E = ℝ`) of the twoPL density at `θ` is, at every response
pattern `Y`, `∑ j, a j * ((if Y j then 1 else 0) - p_j (θ))` with
`p_j (θ) = Real.sigmoid (a j * (θ - b j))`. No new score definition is
introduced.
