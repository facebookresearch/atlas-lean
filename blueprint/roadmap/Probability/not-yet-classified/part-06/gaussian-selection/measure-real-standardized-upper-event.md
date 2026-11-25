# The selected proportion of a Gaussian score

Let `μ` be a probability measure on `Ω`,
`f : Ω → ℝ` a random variable with a Gaussian law under `μ` and `Var[f; μ] > 0`, and `z ∈ ℝ`.
Then the probability of the standardized upper event `{ω | μ[f] + z σ_f ≤ f ω}` is the standard
normal upper tail at `z`, written `Φ(-z) = cdf (gaussianReal 0 1) (-z)`.
