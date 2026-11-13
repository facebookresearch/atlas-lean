# Atteson's theorem: neighbor joining has `ℓ∞` radius `1/2`

**Atteson's theorem: neighbor joining has `ℓ∞` radius `1/2`** (Atteson 1999). Let `d` be
the path-length metric of a binary phylogenetic `X`-tree `(G, ι)` with positive edge lengths
`w`, let `μ` be a lower bound on the lengths of its internal edges (edges with no taxon at
either end), and let `D` be a symmetric dissimilarity with zero diagonal such that
`|D x y - d x y| < μ / 2` for all distinct taxa. Then every complete run of neighbor joining on
`D` (stopped with at most three clusters) forms exactly the splits of the internal edges of the
tree: a set of taxa `A` or its complement is a formed cluster if and only if `A` is the set of
taxa on the `a`-side of an edge `{a, b}` with both endpoints internal.

## Sources

- Atteson (1999); stated as Theorem 2 of Mihaescu, Levy and Pachter (2009). `NJRun` uses the Studier–Keppler update. The proof was written for this formalization: up to row shifts, which do not change the pairs neighbor joining selects, the cluster dissimilarity of a run is an average of `D` (`NJRun.exists_avg`), so its errors against the tree metric of the current clusters stay below `μ / 2`, and the cherry step `exists_eq_pair_of_qCriterion_min_of_abs_sub_lt` applies at every join.
