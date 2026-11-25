# On the inverse domain the transition proportion is recovered

`P(M, i)` and `Q(M, i)` are the [transition](transition-prop.md) and
[transversion](transversion-prop.md) proportions in row `i` of a matrix `M`. If `1 - 2Q > 0` and
`1 - 2P - Q > 0`, then for every nucleotide `i` the [Kimura matrix](kimura-prob.md) at the recovered
parameters has transition proportion `P`: `P(T(a(P, Q), b(Q)), i) = P`, where `a` is the
[transition parameter](kimura-transition-param.md)
`a(P, Q) = -(1/2) · log (1 - 2P - Q) + (1/4) · log (1 - 2Q)` and `b` the
[transversion parameter](kimura-transversion-param.md) `b(Q) = -(1/4) · log (1 - 2Q)`. The recovered
parameters may be negative. With the transversion counterpart and the recovery of `a` and `b`, this
makes `(a, b) ↦ (P, Q)` a bijection from `ℝ × ℝ` onto the algebraic domain `1 - 2Q > 0`,
`1 - 2P - Q > 0`.
