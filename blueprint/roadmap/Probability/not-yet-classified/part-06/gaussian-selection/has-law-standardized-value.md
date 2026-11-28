# Standardizing a Gaussian score

Let `μ` be a measure on `Ω` and `f : Ω → ℝ` a random
variable with a Gaussian law under `μ` (`HasGaussianLaw f μ`) and `Var[f; μ] > 0`. Then the
standardized score `standardizedValue μ f = (f - μ[f]) / populationSD μ f` has the standard
normal law `gaussianReal 0 1` under `μ`.
