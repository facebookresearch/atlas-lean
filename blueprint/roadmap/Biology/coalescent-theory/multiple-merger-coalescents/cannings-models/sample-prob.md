# Probability of an event for the parents of a sample

For a [Cannings model](cannings-model.md) of a population of size `N`, a sample size `m` and an
event `E` on maps `{0, …, m - 1} → {0, …, N - 1}`, the sample probability of `E` is the
probability that the parents `(f(0), …, f(m - 1))` of the first `m` children satisfy `E`. By
[exchangeability in the children](sum-law-comp-emb.md) it is the probability of `E` for the
parents of any `m` distinct children, that is, for a sample of `m` lineages traced back one
generation. It is defined to be `0` when `m > N`.
