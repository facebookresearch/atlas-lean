# The finite-family minimizer is an empirical risk minimizer

For a nonempty finite family
`h : Fin M → H` and a nonempty sample `S`, the member selected by `ProbabilityTheory.ermIdx` for the
losses `f j := L (h j)` minimizes the empirical risk over `Set.range h`.
