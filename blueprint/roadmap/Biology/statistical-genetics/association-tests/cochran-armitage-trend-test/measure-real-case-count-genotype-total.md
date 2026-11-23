# Conditional null law of the fixed-margin case–control table

Let `ι` be a finite set of genotype classes, every singleton of which is measurable, `P` a
probability measure, `R, S ∈ ℕ`, and `G_0, …, G_{R+S−1}` random genotype classes that are
independent under `P`: the `R` cases `G_k`, `k < R`, with law `π_case`, and the `S` controls `G_k`,
`R ≤ k < R + S`, with law `π_ctrl`. Suppose the null hypothesis `π_case = π_ctrl`. Then for all
count vectors `r, n : ι → ℕ`,

`P(case counts = r and genotype margin = n) = H(R; n, r) · P(genotype margin = n)`,

where the [case counts](case-count-2.md) are those of the subjects `k < R`, the
[genotype margin](genotype-total.md) counts all `R + S` subjects, and `H` is the
[multivariate hypergeometric mass](mv-hypergeometric-real.md), with `∑ᵢ nᵢ = R + S` on the event.
For a margin `n` of positive probability, the case counts given the margin have the law
`H(R; n, ·)`, which does not depend on the common genotype law; the identity, stated without
division, also holds for margins of probability zero.

## Sources

- N. Mantel, *Chi-square tests with one degree of freedom; extensions of the Mantel–Haenszel
  procedure*, J. Amer. Statist. Assoc. 58 (1963), 690–700.
