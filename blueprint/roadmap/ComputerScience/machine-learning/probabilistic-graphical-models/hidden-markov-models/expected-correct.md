# Posterior expected number of correctly decoded states

The posterior expected number of correctly decoded states of a path `z`: the sum over all
state paths `w` of `pathProb w / likelihood` times the number of times `t ≤ T` with
`w t = z t`. When the weights are probabilities and the likelihood is positive, this is the
expectation under the posterior law of the path; for likelihood `0` it is `0` (`x / 0 = 0`), as
is every posterior `smoothed`.
