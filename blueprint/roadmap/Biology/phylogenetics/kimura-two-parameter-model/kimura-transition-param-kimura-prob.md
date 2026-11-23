# Recovery of the transition parameter

`P(M, i)` and `Q(M, i)` are the [transition](transition-prop.md) and
[transversion](transversion-prop.md) proportions in row `i` of a matrix `M`. For all real `a` and
`b` and every nucleotide `i`, the [transition parameter](kimura-transition-param.md)
`a(P, Q) = -(1/2) · log (1 - 2P - Q) + (1/4) · log (1 - 2Q)` returns `a` from the proportions of the
[Kimura matrix](kimura-prob.md): `a(P(T(a, b), i), Q(T(a, b), i)) = a`.
