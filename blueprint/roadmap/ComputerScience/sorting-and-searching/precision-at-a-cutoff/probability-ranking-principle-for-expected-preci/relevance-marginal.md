# Relevance Marginal

The marginal relevance of document `i` under finite joint relevance
weights `μ`: the total weight of the relevance vectors with `rel i = true`.

`μ rel` is the weight of the full relevance vector `rel : Fin N → Bool`.
No independence assumption is made: `μ` may be any joint law. When `μ` is a
probability mass function, this is the probability that `i` is relevant.
