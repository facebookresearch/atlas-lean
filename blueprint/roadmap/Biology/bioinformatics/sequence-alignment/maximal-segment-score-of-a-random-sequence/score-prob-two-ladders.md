# The first two ladder segments are independent with the same law

Let `q` be a probability vector and `f` real scores on a finite alphabet, and let `k`, `k'` and `n`
be natural numbers with `k + k' ≤ n`. For properties `A` and `B` of score lists, the probability,
for the scores of `n` independent letters with law `q`, that the first `k` scores
[end at the first strict ascending ladder epoch](is-first-ladder.md) and satisfy `A`, and that the
next `k'` scores end at the first ladder epoch of their own walk and satisfy `B`, is the product of
the probability that `k` scores end at a first ladder epoch and satisfy `A` and the probability
that `k'` scores do so and satisfy `B`.
