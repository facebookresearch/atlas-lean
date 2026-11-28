# Second-order bounds with the pairwise dependence coefficient

Let `p` and `q` be
[probability vectors](../../../../ComputerScience/machine-learning/bayesian-inference-and-sampling/expectation-maximization-algorithm/is-dist.md)
on a finite alphabet, `s` a real score on pairs of letters, `m` and `n` natural numbers and
`t ≥ 0`. Then the [maximal ungapped alignment score](max-align-score.md) `M_{m,n}` of independent
words of `m` and `n` independent letters with laws `p` and `q` satisfies, at every finite size,
`1 - ∑_d p_d ≤ P(M_{m,n} ≤ t) ≤ 1 - ∑_d p_d + e_2(p_·) + Δ_2`. The sums run over the
[offsets](offsets.md) `-m < d < n`, `p_d` is the [exceedance probability](exceed-prob.md) of
diagonal `d`, `e_2(p_·) = ∑_{d < d'} p_d p_{d'}` is the [elementary symmetric sum](elem-symm.md) of
order `2` and `Δ_2` is the pairwise [cross-diagonal dependence coefficient](cross-dep.md).
