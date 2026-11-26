# Current Rate

The contracted current rate function `I(j) = inf_p I(p, j)`, with values in `[0, ∞]`: for a
conservative current `j` it is the infimum of `I(p, j)` over positive probability densities `p`,
and for a non-conservative current it is `+∞`, as in the source. Each `I(p, j)` is a sum of terms
`Ψ(j, j^p, a^p)` over the edges; for nonnegative rates (as in `Setting`), a positive `p` and a
conservative `j`, every term is nonnegative, since `Ψ(·, j̄, a)` is convex and nonnegative for
`a > 0`, and an edge with `a^p = 0` has zero reverse rate, where a conservative `j` vanishes.
