# Probability of non-identity by descent under fluctuating population size

The probability `h t` that two distinct gene copies of generation `t` are not identical by
descent, in a neutral Wright–Fisher population of diploids of size `N i` in generation `i`, given
the identity by descent `R` of generation `0`. The genealogy is uniformly random, and the two
gene copies `a ≠ b` are drawn uniformly at random, independently of it: `h t` is the proportion of
triples `(g, a, b)` with `a ≠ b` for which `a` and `b` are not identical by descent under `g`. So
`h 0` is the proportion of ordered pairs of distinct gene copies of generation `0` that `R` does
not relate. This is a probability when the sizes are positive through the sampled generation,
`N i ≥ 1` for every `i ≤ t`. Otherwise there is no triple to draw, as no genealogy exists or
generation `t` has fewer than two gene copies, and `h t = 0 / 0 = 0` by the convention
`x / 0 = 0`: an empty sample is not a uniform draw.
