# BDe marginal likelihood of a variable set

The (unnormalized) marginal likelihood of the data restricted to the variables `S` under
the BDe Dirichlet prior on the joint values of `S`. `p` is treated as generalized weights
here: the total Dirichlet mass over configurations is `ess * ∑ x, p x`, so the omitted
normalizing factor is `1 / rising (ess * ∑ x, p x) D.length`, the same for every `S`. When
`p` is normalized (`∑ x, p x = 1`) this is `1 / rising ess D.length`, and `p` is a prior
joint distribution.
