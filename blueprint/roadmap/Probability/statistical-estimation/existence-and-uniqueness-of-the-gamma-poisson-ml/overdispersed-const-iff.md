# At a common size factor the Pearson condition is M < V

For counts `k₁, …, kₙ` (`n ≥ 1`) with
[sample mean](../../../Probability/statistical-estimation/likelihood-equations-and-efficiency-of-the-gamma/count-mean.md) `M` and
[biased sample variance](../../../Probability/statistical-estimation/likelihood-equations-and-efficiency-of-the-gamma/count-var.md) `V`, and
a common size factor `σ > 0`, the Pearson-type overdispersion condition `∑ᵢ (kᵢ - σ μ̂)² > ∑ᵢ kᵢ`,
with the [pooled Poisson rate](pooled-mean.md) `μ̂ = (∑ᵢ kᵢ) / (n σ)`, holds if and only if `M < V`.
Indeed `σ μ̂ = M`, `∑ᵢ (kᵢ - M)² = n V` and `∑ᵢ kᵢ = n M`.
