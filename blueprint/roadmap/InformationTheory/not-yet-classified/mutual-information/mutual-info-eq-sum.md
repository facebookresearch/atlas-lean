# Mutual Info eq sum

The explicit finite-sum form of mutual information in nats:
`∑ x y, p (x, y) log (p (x, y) / (pX x * pY y))`, where the marginals
are the finite sums. Real-arithmetic conventions make terms with
`p (x, y) = 0` contribute `0`. Proved from `toReal_klDiv_prod` and the
bits API, not assumed as a definition.
