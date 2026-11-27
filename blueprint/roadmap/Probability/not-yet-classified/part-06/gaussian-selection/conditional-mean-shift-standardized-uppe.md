# Response to truncation selection on a Gaussian score

Let `μ` be a probability measure
on `Ω`, and `H, I : Ω → ℝ` random variables with `I` measurable, `(H, I)` jointly Gaussian under
`μ` (`HasGaussianLaw (fun ω => (H ω, I ω)) μ`) and `Var[I; μ] > 0`. Then for every threshold
`z ∈ ℝ`, selecting the standardized upper event of `I` at `z` shifts the mean of `H` by
`inverseMillsRatio (-z) * (cov[I, H; μ] / populationSD μ I)`.
