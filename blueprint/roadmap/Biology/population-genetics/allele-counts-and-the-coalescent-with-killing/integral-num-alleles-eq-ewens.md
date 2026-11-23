# Coalescent and Ewens formula give the same expected allele count

Let `θ > 0` and `n ≥ 1`, and let `K_n` be the [number of alleles](num-alleles.md) of a
[coalescent with killing](killing-coalescent.md) of a sample of `n` genes on a probability space
`(Ω, μ)`, whose clocks are mutually independent exponential variables of rates `k (k - 1) / 2`
(coalescence) and `k θ / 2` (mutation) at the levels `2 ≤ k ≤ n`. Then `∫ K_n dμ = ∑_π E_θ(π) |π|`,
the mean number of alleles under the
[Ewens sampling formula](../ewens-sampling-formula-and-the-chinese-restauran/ewens-prob.md): the sum
runs over the integer partitions `π` of `n`, `E_θ(π)` is the Ewens probability of `π` and `|π|` its
number of parts.
