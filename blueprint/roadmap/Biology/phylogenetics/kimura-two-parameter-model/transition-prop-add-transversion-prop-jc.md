# On Jukes–Cantor data P + Q is the probability of a difference

`P(M, i)` and `Q(M, i)` are the [transition](transition-prop.md) and
[transversion](transversion-prop.md) proportions in row `i` of a matrix `M`. For all real `μ` and
`t` and every nucleotide `i`, the two proportions of the
[Jukes–Cantor transition probability](../jukes-cantor-model/jc-prob.md) matrix `M` (entries
`1/4 + 3/4 · e^(-4μt/3)` on the diagonal and `1/4 - 1/4 · e^(-4μt/3)` off it) add up to the
[probability that the ends of a branch differ](../jukes-cantor-model/p-diff.md):
`P(M, i) + Q(M, i) = ∑_{j ≠ i} M i j`.
