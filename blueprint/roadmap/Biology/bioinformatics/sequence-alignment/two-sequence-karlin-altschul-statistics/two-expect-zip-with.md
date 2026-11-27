# Letter-by-letter scores of two independent iid words are iid

Let `p` and `q` be
[probability vectors](../../../../ComputerScience/machine-learning/bayesian-inference-and-sampling/expectation-maximization-algorithm/is-dist.md)
on a finite alphabet, `s` a real score on pairs of letters, `m` and `n` natural numbers and `F` a
real functional of score lists. For independent words `u` and `v` of `m` and `n` independent
letters with laws `p` and `q` ([two-sequence model](two-expect.md)), the expectation of
`F(s(u₀, v₀), …, s(u_{k-1}, v_{k-1}))` with `k = min(m, n)` equals the
[average over score sequences](../../../../Probability/random-walks/maximal-segment-score-of-a-random-sequence/score-expect.md) of
length `min(m, n)` of `F` for the [pair law](pair-law.md) and the [pair score](pair-score.md). So
the scores of the first `min(m, n)` aligned pairs are independent copies of `s(A, B)`, with `A` of
law `p` and `B` of law `q` independent.
