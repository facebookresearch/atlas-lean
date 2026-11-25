# No design matrix has full column rank when edges outnumber pairs

Let `P` be a finite set of `n` populations, `E` a finite set of edges and `w(X, e)` any real lineage
weights, with more edges than pairs of distinct populations, `n choose 2 = n (n - 1) / 2 < |E|`.
Then for every family of quadruples `(A_i, B_i, C_i, D_i)` of populations, indexed by an arbitrary
set, the [design matrix](../fitting-admixture-graphs-by-least-squares/design-matrix.md) `B`,
`B_ie = (w(A_i, e) - w(B_i, e)) (w(C_i, e) - w(D_i, e))`, does not have full column rank: the linear
map `ℓ ↦ B ℓ` is not injective, so `B v = 0` for some nonzero `v`. Hence, by
[the non-identifiability result](exists-len-ne-of-not-injective.md), no family of f4 statistics
determines the drift lengths.
