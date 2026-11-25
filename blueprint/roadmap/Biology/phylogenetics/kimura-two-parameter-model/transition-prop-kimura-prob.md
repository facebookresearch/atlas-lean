# Transition proportion of the Kimura matrix

`P(M, i)` and `Q(M, i)` are the [transition](transition-prop.md) and
[transversion](transversion-prop.md) proportions in row `i` of a matrix `M`. For all real `a` and
`b` and every nucleotide `i`, the transition proportion of the [Kimura matrix](kimura-prob.md)
`T(a, b)` in row `i` is `P(T(a, b), i) = 1/4 + 1/4 · e^(-4b) - 1/2 · e^(-2(a + b))`, whatever the
starting base.
