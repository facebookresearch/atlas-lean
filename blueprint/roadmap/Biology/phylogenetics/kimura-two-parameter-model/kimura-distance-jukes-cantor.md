# The Kimura distance reduces to the Jukes–Cantor distance

`P(M, i)` and `Q(M, i)` are the [transition](transition-prop.md) and
[transversion](transversion-prop.md) proportions in row `i` of a matrix `M`. For all real `μ` and
`t` and every nucleotide `i`, let `M` be the [Jukes–Cantor matrix](../jukes-cantor-model/jc-prob.md)
(entries `1/4 + 3/4 · e^(-4μt/3)` on the diagonal and `1/4 - 1/4 · e^(-4μt/3)` off it; it is a
transition probability matrix when `μ t ≥ 0`), and `P = P(M, i)`, `Q = Q(M, i)` its transition and
transversion row weights. Then the [Kimura distance](kimura-distance.md)
`d(P, Q) = -(1/2) · log (1 - 2P - Q) - (1/4) · log (1 - 2Q)` equals the
[Jukes–Cantor distance](../jukes-cantor-model/jc-distance.md) `d_JC(p) = -(3/4) · log (1 - 4p/3)` of
`p = P + Q`: `d(P, Q) = d_JC(P + Q)`, and both equal `μ t`.
