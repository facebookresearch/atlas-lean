# Survival criterion

For `p ∈ [0, 1]`, the survival probability is `0` iff the mean `b p`
is at most `1`, except in the deterministic case `b = p = 1` (every vertex has exactly one open
child), where the mean is `1` but the survival probability is positive. Away from that case this
is `MathlibExt.Probability.GaltonWatson.extinctionProb_eq_one_iff` for the offspring law
`Binomial(b, p)`.
