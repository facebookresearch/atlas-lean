# Probability that two gene copies come from the same parent

For a parent map
`parent : Fin (2 * N) → Fin N`, the probability that an ordered pair $(a, b)$ of distinct gene
copies of the offspring generation, chosen uniformly at random among the $2N(2N - 1)$ such pairs,
has $\mathrm{parent}(a) = \mathrm{parent}(b)$. It is $0$ when $N = 0$, as there is no such
pair.
