# A diagonal's exceedance probability is a one-sequence tail probability

For [probability vectors](../../../../ComputerScience/machine-learning/bayesian-inference-and-sampling/expectation-maximization-algorithm/is-dist.md)
`p` and `q` on a finite alphabet, a real score `s` on pairs of letters, natural numbers `m` and
`n`, a real `t` and an integer `d`, the [exceedance probability](exceed-prob.md) `p_d` equals the
[score probability](../../../../Probability/random-walks/maximal-segment-score-of-a-random-sequence/score-prob.md) that the
[maximal segment score](../../../../Probability/random-walks/maximal-segment-score-of-a-random-sequence/max-seg-score.md) of `L`
independent letter pairs with the [pair law](pair-law.md), scored by the
[pair score](pair-score.md), is greater than `t`, where `L = min(m - (-d)⁺, n - d⁺)` is the
[diagonal length](diag-len.md).
