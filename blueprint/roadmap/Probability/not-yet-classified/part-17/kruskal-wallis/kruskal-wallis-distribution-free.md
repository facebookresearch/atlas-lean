# Distribution-freeness

Let `μ`
be a probability measure, `X_1, …, X_N : Ω → ℝ` independent measurable random variables with a
common law (`X_k` and `X_l` have the same law for all `k, l`) that has no atoms, and `g` an
assignment of the `N` positions to `C` samples. For every real `h`, the probability that the
ranks `sampleRank (fun j => X_j) k = 1 + #{j | X_j < X_k}` are `σ k + 1` for a permutation `σ` of
`Fin N` whose Kruskal–Wallis statistic is
`h` equals the number of permutations `σ` with `H(σ) = h`, divided by `N!`. (The ranks form a
permutation almost surely, so this is the law of `H` of the sample ranks.)

## Sources

- W. H. Kruskal and W. A. Wallis, "Use of ranks in one-criterion variance analysis", J. Amer. Statist. Assoc. 47 (1952) 583–621, Section 1; W. H. Kruskal, "A nonparametric test for the several sample problem", Ann. Math. Statist. 23 (1952) 525–540, p. 525.
