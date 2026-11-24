# Berry–Esseen bound for Mendelian draws, explicit variance form

Let `P` be a probability measure, and let the offspring allele counts `X_l` (`l ∈ ℕ`) be
measurable and mutually independent (unlinked loci), each `X_l` with the
[Mendelian offspring law](mendel-law.md) of parents carrying `g₁(l), g₂(l) ≤ 2` focal alleles.
Write `pᵢ(l) = gᵢ(l) / 2`. If `|a_l| ≤ B / √M` for `l < M`, `σ > 0` and
`∑_{l < M} a_l² (p₁(l) (1 - p₁(l)) + p₂(l) (1 - p₂(l))) = σ²` (the sum is the variance of the
[segregation deviation](segregation-deviation.md) `R_M`), then for every real `x`,
`|P(R_M ≤ x) - Φ(x / σ)| ≤ 336 B³ / (σ³ √M)`, where `Φ` is the standard normal distribution
function.
