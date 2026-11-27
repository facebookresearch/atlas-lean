# Probability that a random mutation is beneficial

For a phenotype `a ∈ ℝⁿ`, with the optimum at `0`, and a real mutation size `r`, the beneficial
probability is the probability, for `G` with the standard Gaussian law on `ℝⁿ`, that
`‖a + r u‖ < ‖a‖` with `u = ‖G‖⁻¹ G` the [Gaussian direction](gauss-direction.md). For `n ≥ 1`, `u`
is a uniformly random unit direction (the event `G = 0`, where `u = 0` by the convention `0⁻¹ = 0`,
has probability `0`), and for `r ≥ 0` this is the probability that a mutation of size `r` in a
uniformly random direction moves the phenotype strictly closer to the optimum (for `r < 0` the
displacement `r u` has length `|r|` and direction `-u` when `G ≠ 0`, so almost surely). In dimension
`n = 0` there is no unit direction: the space is `{0}`, so `G = 0` and `u = 0` surely, the event is
empty and the value is `0`.
