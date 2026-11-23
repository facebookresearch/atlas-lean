# Probability that a diagonal has a segment scoring above a threshold

For real weights `p` and `q` on a finite alphabet, a real score `s` on pairs of letters, natural
numbers `m` and `n`, a real `t` and an integer `d`, the exceedance probability `p_d` is the
[two-sequence probability](two-prob.md), over words `u` and `v` of lengths `m` and `n`, that the
[maximal segment score](../../../../Probability/random-walks/maximal-segment-score-of-a-random-sequence/max-seg-score.md) of the
[diagonal of offset](diag.md) `d` of `u` and `v` is greater than `t`. When `p` and `q` are
[probability vectors](../../../../ComputerScience/machine-learning/bayesian-inference-and-sampling/expectation-maximization-algorithm/is-dist.md),
it is the probability that diagonal `d` of independent words of independent letters with laws `p`
and `q` contains a segment scoring more than `t`. For an offset outside `-m < d < n` the diagonal
is empty; for probability vectors `p_d` is then `1` if `t < 0` and `0` if `t ≥ 0`.
