# Berry–Esseen bound for Mendelian draws

Let `P` be a probability measure, and let the offspring allele counts `X_l` (`l ∈ ℕ`) be
measurable and mutually independent (unlinked loci), each `X_l` with the
[Mendelian offspring law](mendel-law.md) of parents carrying `g₁(l)` and `g₂(l)` focal alleles.
If `|a_l| ≤ B / √M` for `l < M` and the [segregation deviation](segregation-deviation.md) has
variance `Var(R_M) = σ²` with `σ > 0`, then for every real `x`,
`|P(R_M ≤ x) - Φ(x / σ)| ≤ 336 B³ / (σ³ √M)`, where `Φ` is the standard normal distribution
function.
