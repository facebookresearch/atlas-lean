# Bootstrap support

**Bootstrap support** (Felsenstein 1985) of the split with side `A` away from `a`, for a
tree estimator `est` and an alignment `M` of `m` sites: the fraction of the `m ^ m` site
resamplings with replacement `w : Fin m → Fin m` (uniform draws, whose site counts are
multinomial) for which the tree estimated from the resampled alignment `M ∘ w` has the
cluster `A`. This is the exact bootstrap proportion; Felsenstein's procedure estimates it from a
sample of resamplings.
