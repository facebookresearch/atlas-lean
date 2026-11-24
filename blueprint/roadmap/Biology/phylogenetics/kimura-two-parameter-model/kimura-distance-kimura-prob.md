# Kimura distance of the Kimura transition matrix

`P(M, i)` and `Q(M, i)` are the [transition](transition-prop.md) and
[transversion](transversion-prop.md) proportions in row `i` of a matrix `M`. For all real `a` and
`b` and every nucleotide `i`, the [Kimura distance](kimura-distance.md)
`d(P, Q) = -(1/2) · log (1 - 2P - Q) - (1/4) · log (1 - 2Q)` of the proportions of the
[Kimura matrix](kimura-prob.md) is `d(P(T(a, b), i), Q(T(a, b), i)) = a + 2b`, that is, `(α + 2β) t`
for `a = α t` and `b = β t`. For `a, b ≥ 0` this is the expected number of substitutions per site.
