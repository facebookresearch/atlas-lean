# Below one half the transversion proportion is recovered

`P(M, i)` and `Q(M, i)` are the [transition](transition-prop.md) and
[transversion](transversion-prop.md) proportions in row `i` of a matrix `M`. If `1 - 2Q > 0`, that
is `Q < 1/2`, then for every real `P` and every nucleotide `i`, the [Kimura matrix](kimura-prob.md)
at the recovered parameters `a(P, Q)` and `b(Q)` has transversion proportion `Q`:
`Q(T(a(P, Q), b(Q)), i) = Q`, where `a` is the [transition parameter](kimura-transition-param.md)
`a(P, Q) = -(1/2) · log (1 - 2P - Q) + (1/4) · log (1 - 2Q)` and `b` the
[transversion parameter](kimura-transversion-param.md) `b(Q) = -(1/4) · log (1 - 2Q)`, with the
conventions `log 0 = 0` and `log x = log |x|` for `x < 0`. The argument `1 - 2P - Q` of `a(P, Q)`
may be zero or negative; the transversion proportion of `T(a, b)` does not depend on `a`, so no
condition on `P` is needed. At `Q = 1/2` the recovered `b(1/2) = 0` gives `Q(T(a, 0), i) = 0`, not
`1/2`.
