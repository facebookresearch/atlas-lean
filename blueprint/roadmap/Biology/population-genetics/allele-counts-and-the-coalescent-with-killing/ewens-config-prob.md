# Ewens sampling formula on allele-count configurations

For a real `θ`, a sample size `n` and a sequence `a = (a_1, a_2, …)` of natural numbers, the Ewens
sampling formula in configuration form (Ewens 1972) is
`P(a_1, …, a_n) = n! / (θ (θ + 1) ⋯ (θ + n - 1)) · ∏_{j=1}^n (θ / j) ^ {a_j} / a_j!`.
Only the values `a_1, …, a_n` enter. It is defined for every real `θ`: when
`θ (θ + 1) ⋯ (θ + n - 1) = 0`, that is for `θ ∈ {0, -1, …, -(n - 1)}`, the convention `x / 0 = 0`
makes it `0`. The intended domain is `θ > 0` (the scaled mutation rate `θ = 4Nu`), where, for a
configuration with `∑_{j=1}^n j a_j = n`, it is the probability that the sample has
[configuration `a`](sum-ewens-prob-allele-count-eq.md); no sample of `n` genes has a configuration
with `∑_{j=1}^n j a_j ≠ n`.
