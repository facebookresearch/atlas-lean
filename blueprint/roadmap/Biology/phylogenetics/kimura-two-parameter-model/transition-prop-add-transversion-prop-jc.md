# Transition and transversion weights sum to the Jukes–Cantor difference

`P(M, i)` and `Q(M, i)` are the [transition](transition-prop.md) and
[transversion](transversion-prop.md) proportions in row `i` of a matrix `M`. For all real `μ` and
`t` and every nucleotide `i`, let `M` be the [Jukes–Cantor matrix](../jukes-cantor-model/jc-prob.md)
with entries `1/4 + 3/4 · e^(-4μt/3)` on the diagonal and `1/4 - 1/4 · e^(-4μt/3)` off it. Then its
two row weights add up to the off-diagonal row sum
`P(M, i) + Q(M, i) = ∑_{j ≠ i} M i j = 3/4 · (1 - e^(-4μt/3))`, the
[Jukes–Cantor difference](../jukes-cantor-model/p-diff.md). The identity holds for all real `μ` and
`t`; the sum is a probability, that the two ends of a branch differ, when `μ t ≥ 0`, and is negative
when `μ t < 0`.
