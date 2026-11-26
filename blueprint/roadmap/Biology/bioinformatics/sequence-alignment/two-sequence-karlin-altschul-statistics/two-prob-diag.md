# Events along one diagonal have their one-sequence probability

Let `p` and `q` be
[probability vectors](../../../../ComputerScience/machine-learning/bayesian-inference-and-sampling/expectation-maximization-algorithm/is-dist.md)
on a finite alphabet, `s` a real score on pairs of letters, `m` and `n` natural numbers, `d` an
integer and `P` a property of score lists. For independent words of `m` and `n` independent
letters with laws `p` and `q`, the [probability](two-prob.md) that the
[diagonal of offset](diag.md) `d` satisfies `P` equals the
[score probability](../../../../Probability/random-walks/maximal-segment-score-of-a-random-sequence/score-prob.md) of `P` for
`L` independent letter pairs with the [pair law](pair-law.md), scored by the
[pair score](pair-score.md), where `L = min(m - (-d)⁺, n - d⁺)` is the
[diagonal length](diag-len.md).
