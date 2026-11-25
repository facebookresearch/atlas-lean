# Kimura distance of the K80 matrix exponential

Write `R_κ` for the [K80 rate matrix](../time-reversible-nucleotide-substitution-models/k80-rate.md)
with transition/transversion ratio `κ`: `-(κ + 2)/4` on the diagonal, `κ/4` for a transition and
`1/4` for a transversion. `P(M, i)` and `Q(M, i)` are the [transition](transition-prop.md) and
[transversion](transversion-prop.md) proportions in row `i` of a matrix `M`. For all real `κ` and
`t` and every nucleotide `i`, the [Kimura distance](kimura-distance.md)
`d(P, Q) = -(1/2) · log (1 - 2P - Q) - (1/4) · log (1 - 2Q)` of the transition and transversion row
weights of `exp (t · R_κ)` in row `i` is `(κ + 2) t / 4 = (-R_κ i i) · t`. For `κ ≥ 0`,
`-R_κ i i = (κ + 2)/4` is the total substitution rate out of each base; if also `t ≥ 0`, the weights
are proportions of a K80 transition probability matrix and the distance is the expected number of
substitutions per site over time `t`. For `κ < -2` the coefficient `(κ + 2)/4` is negative, so it is
not a rate.
