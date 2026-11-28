# The scores along one diagonal form an iid pair-score sequence

Let `p` and `q` be
[probability vectors](../../../../Probability/not-yet-classified/is-dist.md)
on a finite alphabet, `s` a real score on pairs of letters, `m` and `n` natural numbers, `d` an
integer and `F` a real functional of score lists. For independent words of `m` and `n`
independent letters with laws `p` and `q` ([two-sequence model](two-expect.md)), the expectation
of `F` of the [diagonal of offset](diag.md) `d` equals the
[average over score sequences](../../../../Probability/random-walks/maximal-segment-score-of-a-random-sequence/score-expect.md) of
length `L = min(m - (-d)⁺, n - d⁺)`, the [diagonal length](diag-len.md), of `F` for the
[pair law](pair-law.md) and the [pair score](pair-score.md). So the scores along each diagonal are
`L` independent copies of `s(A, B)`, and results on iid score sequences apply to each diagonal
separately. For `d` outside `-m < d < n` the diagonal is empty and both sides are `F` of the
empty list.
