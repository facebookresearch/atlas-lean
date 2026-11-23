# Overdispersion gives a solution of the score equations

At a common size factor
`σ > 0`, if the sample is overdispersed, `0 < M < V` (exactly the condition under which the moment
estimates `momShape M V`, `momRate σ M V` are positive), then the score equations of the marginal
likelihood have a solution `(â, σ â / M)` with `â > 0`. Uniqueness and global maximality are
`existsUnique_score_root` and `logMarginalLik_lt_of_score_root` in
`Domains.Biology.Omics.HierarchicalCountMLEUniqueness`.
