# Validity of the exact allelic test under the binomial null

Let `μ` be a probability measure on `Ω`, `n₁` and `n₂` natural numbers, `0 < f < 1`, and
`X, Y : Ω → ℕ` measurable allele counts that are independent under `μ`, with `X` of law `Bin(n₁, f)`
and `Y` of law `Bin(n₂, f)`: the null of no association, with one allele frequency `f` in cases and
controls. Then the [allelic p-value](allelic-pvalue.md) `p` is a
[valid p-value](../valid-p-values-and-false-discovery-proportion/is-valid-pvalue.md)
under `μ`: `μ{ω : p(ω) ≤ s} ≤ s` for every `s ∈ [0, 1]`. The bound holds for every such `f`, which
need not be known.

The statement assumes this null. It is a per-variant statement and says nothing about the joint law
of the p-values of different variants.

## Sources

- Lehmann–Romano (2005), §4.5 and Lemma 3.3.1.
