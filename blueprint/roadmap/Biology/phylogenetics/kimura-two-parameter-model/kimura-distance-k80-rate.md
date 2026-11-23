# Kimura distance of the K80 transition matrix

Write `R_κ` for the [K80 rate matrix](../time-reversible-nucleotide-substitution-models/k80-rate.md)
with transition/transversion ratio `κ`: `-(κ + 2)/4` on the diagonal, `κ/4` for a transition and
`1/4` for a transversion. `P(M, i)` and `Q(M, i)` are the [transition](transition-prop.md) and
[transversion](transversion-prop.md) proportions in row `i` of a matrix `M`. For all real `κ` and
`t` and every nucleotide `i`, the [Kimura distance](kimura-distance.md)
`d(P, Q) = -(1/2) · log (1 - 2P - Q) - (1/4) · log (1 - 2Q)` of the proportions of `exp (t · R_κ)`
in row `i` is `(κ + 2) t / 4`: the total substitution rate `-R_κ i i = (κ + 2)/4` times `t`.
