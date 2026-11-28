# Allelic p-values meet the genome-wide assumptions under their nulls

Let `μ` be a probability measure on `Ω`, `H0` a subset of `{0, …, m - 1}` and `r` a
[dependence regime](dependence-regime.md), and for each of `m` variants `i` let
`X i, Y i : Ω → ℕ` be measurable allele counts among `n₁ i` case and `n₂ i` control alleles.
Suppose that every `i ∈ H0` satisfies the allelic null with its own frequency: `0 < f i < 1`, and
`X i` and `Y i` are independent under `μ` with laws `Bin(n₁ i, f i)` and `Bin(n₂ i, f i)`. Suppose
also that the [allelic p-values](allelic-pvalue.md) `p i` of the variants satisfy the
[hypothesis of the regime](holds.md) `r`. Then `p` satisfies the
[genome-wide assumptions](genome-wide-assumptions.md) for `μ`, `H0` and `r`. The dependence
hypothesis is an input, not a consequence of the nulls.
