# Ewens sampling formula on allele-count configurations

For a real `θ`, a sample size `n` and a sequence `a = (a_1, a_2, …)` of natural numbers, the Ewens
sampling formula in configuration form (Ewens 1972) is
`P(a_1, …, a_n) = n! / (θ (θ + 1) ⋯ (θ + n - 1)) · ∏_{j=1}^n (θ / j) ^ {a_j} / a_j!`.
Only the values `a_1, …, a_n` enter. It is defined for every real `θ`: when
`θ (θ + 1) ⋯ (θ + n - 1) = 0`, that is when `θ = -i` for an integer `i` with `0 ≤ i < n`, the
convention `x / 0 = 0` makes it `0`. For `n = 0` the products are empty and the value is `1` for
every `θ`. The intended domain is `θ > 0` (the scaled mutation rate `θ = 4Nu`), where, for a
configuration with `∑_{j=1}^n j a_j = n`, it is the probability that the configuration of the
sample [agrees with `a` at `j = 1, …, n`](sum-ewens-prob-allele-count-eq.md). No sample of `n`
genes has a configuration with `∑_{j=1}^n j a_j ≠ n`, so such an `a` has probability `0`, while
the formula need not vanish there: for `n = 1`, `a_1 = 0` and `θ = 1` it is `1`.
