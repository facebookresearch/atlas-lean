# Berry–Esseen bound for the segregation deviation

Let `P` be a probability measure (the law conditional on the parents) and let the offspring allele
counts `X_l` (`l ∈ ℕ`) be measurable, mutually independent (unlinked loci) and almost surely in
`[0, 2]`. Let the additive effects satisfy `|a_l| ≤ B / √M` for `l < M`, and let the
[segregation deviation](segregation-deviation.md) have variance `Var(R_M) = σ²` with `σ > 0`
(which forces `M ≥ 1`). Then for every real `x`,
`|P(R_M ≤ x) - Φ(x / σ)| ≤ 336 B³ / (σ³ √M)`, where `Φ` is the standard normal distribution
function. The constant is `336 = 42 · 2³`: each summand `a_l (X_l - E X_l)` is bounded by
`2 |a_l|`, and the Lyapunov form of the Berry–Esseen bound used has constant `42`.
