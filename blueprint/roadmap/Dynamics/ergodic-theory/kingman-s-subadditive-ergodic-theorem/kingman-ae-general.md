# Kingman's subadditive ergodic theorem

**Kingman's subadditive ergodic theorem** (J. F. C. Kingman, *The ergodic theory of
subadditive stochastic processes*, 1968): if `X` is a subadditive cocycle over a map `T`
preserving the finite measure `μ` and `inf_n (∫ X n dμ) / n > -∞`, then `X n / n` converges
`μ`-almost everywhere to the finite limit `kingmanLimit T X`. The sign of `X` is arbitrary.
Invariance and integrability of the limit, and `∫ kingmanLimit = gamma`, are not stated here; for
nonnegative cocycles see `exists_invariant_limit_of_nonneg`, which contains
`MathlibExt.Dynamics.Ergodic.KingmanWanted.kingman_subadditive`.
