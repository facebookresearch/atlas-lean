# Odd-order Bonferroni lower bounds for the maximal alignment score

Let `p` and `q` be
[probability vectors](../../../../ComputerScience/machine-learning/bayesian-inference-and-sampling/expectation-maximization-algorithm/is-dist.md)
on a finite alphabet, `s` a real score on pairs of letters, `m` and `n` natural numbers and
`t ≥ 0`. For every natural number `r`, the [maximal ungapped alignment score](max-align-score.md)
`M_{m,n}` of independent words of `m` and `n` independent letters with laws `p` and `q` satisfies
`∑_{k=0}^{2r+1} (-1)^k S_k ≤ P(M_{m,n} ≤ t)`, where `S_k` is the
[exceedance moment](exceed-moment.md) of order `k`, the factorial moment of the number of diagonals
containing a segment scoring more than `t`. Here `S_k = e_k(p_·) + Δ_k`, with `e_k(p_·)` the
[elementary symmetric sum](elem-symm.md) of the [exceedance probabilities](exceed-prob.md) and
`Δ_k` the [cross-diagonal dependence coefficient](cross-dep.md).
