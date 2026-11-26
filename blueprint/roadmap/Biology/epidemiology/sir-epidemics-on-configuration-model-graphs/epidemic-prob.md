# Epidemic Prob

The probability that the epidemic path started from `x₀` lies in `E`, for the random graph
of the degree sequence `d`: the configuration multigraph `G*` (`simple = false`, a uniform
matching) or the uniform simple graph `G` (`simple = true`, a uniform matching conditioned on a
simple multigraph). When no matching qualifies (an odd total degree, or `simple = true` and no
matching gives a simple multigraph), the denominator is `0` and Lean's `x / 0 = 0` convention
makes the value `0` for every `E`. (`hQ` records that each epidemic rate matrix is a rate
matrix.)
