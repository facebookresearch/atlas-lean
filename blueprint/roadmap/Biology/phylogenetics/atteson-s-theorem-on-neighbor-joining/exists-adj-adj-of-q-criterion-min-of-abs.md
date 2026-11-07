# Robust cherry lemma for neighbor joining

The selection step of Atteson's theorem
(Atteson 1999), with a proof after Mihaescu, Levy & Pachter (2009, Theorem 16). Let `d` be
the path-length metric of a binary phylogenetic `X`-tree `(G, ι)` with positive edge lengths
`w` and at least four taxa, and let `μ` be a lower bound on the lengths of the internal edges
(edges with no taxon at either end). Let `D` be a symmetric dissimilarity with zero diagonal
such that `|D x y - d x y| < μ / 2` for all distinct taxa.
If the distinct taxa `x, y` minimize the Q-criterion of `D` over all pairs of distinct
singleton clusters at the start of neighbor joining, then `ι x` and `ι y` have a common
neighbor: they form a cherry. The bound is sharp: with `≤ μ / 2` a non-cherry can tie
(see the tests).
