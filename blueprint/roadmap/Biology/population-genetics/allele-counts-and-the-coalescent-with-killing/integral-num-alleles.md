# Expected number of alleles from the coalescent

Let `θ > 0` and `n ≥ 1`, and let `K_n` be the [number of alleles](num-alleles.md) of a
[coalescent with killing](killing-coalescent.md) of a sample of `n` genes on a probability space
`(Ω, μ)`, whose clocks are mutually independent exponential variables of rates `k (k - 1) / 2`
(coalescence) and `k θ / 2` (mutation) at the levels `2 ≤ k ≤ n`. Then
`E[K_n] = ∫ K_n dμ = ∑_{i=0}^{n-1} θ / (θ + i)` (Ewens 1972; Durrett 2008, §1.3): the term `i = 0`
is the `1` counting the allele of the last remaining lineage, and the term `i = k - 1` is the
[probability `θ / (θ + k - 1)`](measure-real-mutation-first.md) that the event at level `k` is a
killing, for `2 ≤ k ≤ n`. For `n = 1` both sides are `1`.
