# Kimura two-parameter distance

For real proportions `P` of transition and `Q` of transversion differences, the Kimura distance
(Kimura 1980) is `d(P, Q) = -(1/2) · log (1 - 2P - Q) - (1/4) · log (1 - 2Q)`. Its intended domain
is the algebraic domain `1 - 2P - Q > 0`, `1 - 2Q > 0`, and `d` tends to `+∞` when a finite boundary
point of that domain is approached from inside. It is defined for all real `P` and `Q`, with the
conventions `log 0 = 0` and `log x = log |x|` for `x < 0`: a logarithm whose argument is `0`
contributes `0`, and a negative argument `x` contributes `log |x|`; so at a boundary point itself
`d` is finite, for example `d(1/2, 0) = 0`. For the proportions of a K80 transition matrix with
composite parameters `a = α t ≥ 0` and `b = β t ≥ 0` it is the expected number `(α + 2β) t` of
substitutions per site ([recovery](kimura-distance-kimura-prob.md)).
