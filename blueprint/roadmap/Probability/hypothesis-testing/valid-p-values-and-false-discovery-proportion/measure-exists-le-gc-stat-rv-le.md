# Bonferroni bound for the λ̂ tests under arbitrary dependence

Let `P` be any measure on a measurable space `Ω`, `Z_0, …, Z_{m-1}` any real functions on `Ω`
(random scores), `H0` a set of genes (the true nulls) and `s` a real threshold. Suppose the
[corrected statistics](gc-stat-rv.md) satisfy the calibration condition at this threshold,
`P(T_i ≥ s) ≤ P(χ²₁ > s)` for every `i ∈ H0`, where `P(χ²₁ > s)` is the [`χ²₁`
tail](../../../Biology/statistical-genetics/association-tests/genomic-control/chi-sq-one-tail.md). Then

`P(T_i ≥ s for some i ∈ H0) ≤ |H0| · P(χ²₁ > s)`,

where `|H0|` is the number of true nulls. For a probability measure `P`, the test that rejects gene
`i` when `T_i ≥ s` thus rejects some true null with probability at most `|H0| · P(χ²₁ > s)`. This is
the union bound: it needs no assumption on the dependence between the statistics, however strongly
`λ̂` couples them. The scores need not be measurable: `P` of a set that is not measurable is its
outer measure.
