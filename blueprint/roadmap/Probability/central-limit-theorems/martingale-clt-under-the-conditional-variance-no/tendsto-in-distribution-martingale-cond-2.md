# Lindeberg form

Rows of length `n`, square-integrable martingale differences, the
(unconditional) Lindeberg condition `LindebergConditionTriangular`, and the predictable
quadratic variation `∑_{k<n} E[X n k² | F n k] → v` in probability give
`∑_{k<n} X n k → N(0, v)`. The Lindeberg condition implies the conditional one (take
expectations and use Markov's inequality), so this is a corollary of
`tendstoInDistribution_martingale_condVar`.

## Sources

- Hall–Heyde (1980), Corollary 3.1 together with the remark that the Lindeberg condition implies the conditional Lindeberg condition; Brown (1971).
