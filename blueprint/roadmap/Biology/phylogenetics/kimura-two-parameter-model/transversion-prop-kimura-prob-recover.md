# Recovered parameter reproduces the transversion proportion

`P(M, i)` and `Q(M, i)` are the [transition](transition-prop.md) and
[transversion](transversion-prop.md) proportions in row `i` of a matrix `M`. If `1 - 2Q > 0`, then
for every real `P` and every nucleotide `i`, the [Kimura matrix](kimura-prob.md) at the recovered
parameters, `a(P, Q)` and `b(Q)`, has transversion proportion `Q`: `Q(T(a(P, Q), b(Q)), i) = Q`,
where `a` is the [transition parameter](kimura-transition-param.md)
`a(P, Q) = -(1/2) · log (1 - 2P - Q) + (1/4) · log (1 - 2Q)` and `b` the
[transversion parameter](kimura-transversion-param.md) `b(Q) = -(1/4) · log (1 - 2Q)`.
