# Weighted probability of an event on score sequences

For real weights `q` and real scores `f` on a finite alphabet, a natural number `n` and a property
`P` of score lists, the score probability of `P` is the [weighted average](score-expect.md) of the
indicator of `P`: the total weight `∑_w q_{w₀} ⋯ q_{w_{n-1}}` of the words of length `n` whose score
list satisfies `P`. When `q` is a probability vector it is the probability that the scores of `n`
independent letters with law `q` satisfy `P`.
