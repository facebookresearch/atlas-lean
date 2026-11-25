# Finrank Euler01

The difference `dim H⁰(L) - dim H¹(L)` computed with `Module.finrank`. It is the
two-term Euler characteristic only when `H⁰(L)` and `H¹(L)` are finite-dimensional:
`Module.finrank` is `0` on an infinite-dimensional space (for instance, it gives `0`
for the structure sheaf of the affine line). This is the case for line bundles on
proper curves, the scope of the degree lemmas below; other uses must supply
finite-dimensionality.
