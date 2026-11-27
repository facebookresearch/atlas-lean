# Transversion proportion of the Kimura matrix

`P(M, i)` and `Q(M, i)` are the [transition](transition-prop.md) and
[transversion](transversion-prop.md) proportions in row `i` of a matrix `M`. For all real `a` and
`b` and every nucleotide `i`, the transversion proportion of the [Kimura matrix](kimura-prob.md)
`T(a, b)` in row `i` is `Q(T(a, b), i) = 1/2 - 1/2 · e^(-4b)`, whatever the starting base.
Equivalently, `1 - 2 Q(T(a, b), i) = e^(-4b)`.
