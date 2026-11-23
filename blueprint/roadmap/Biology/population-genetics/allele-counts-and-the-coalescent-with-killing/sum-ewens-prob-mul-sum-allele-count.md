# Expected number of alleles in configuration form

For every real `θ > 0` and every sample size `n`, the mean of the number of alleles
`K_n = ∑_{j=1}^n a_j` (with `a` the [allele-count configuration](allele-count.md)) under the
[Ewens sampling formula](../ewens-sampling-formula-and-the-chinese-restauran/ewens-prob.md), a
probability distribution on the allelic partitions of `n`, is
`∑_π E_θ(π) ∑_{j=1}^n a_j(π) = ∑_{i=0}^{n-1} θ / (θ + i)` (Ewens 1972), the sum running over the
integer partitions `π` of `n`, with `E_θ(π)` the Ewens probability of `π`.
