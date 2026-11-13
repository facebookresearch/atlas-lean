# Rank of the reaction graph in complex space

If `G` is the undirected graph on the
complexes `K` in which distinct `c`, `c'` are adjacent exactly when some reaction goes from one
to the other, then the span of the reaction vectors `e_{t r} - e_{s r}` in `ℝ^K` has dimension
`#K - ℓ`, where `ℓ` is the number of connected components (linkage classes) of `G`.

## Sources

- Feinberg (2019), § 6.4; the Laplacian-kernel count is Mathlib's `SimpleGraph.card_connectedComponent_eq_finrank_ker_toLin'_lapMatrix`.
