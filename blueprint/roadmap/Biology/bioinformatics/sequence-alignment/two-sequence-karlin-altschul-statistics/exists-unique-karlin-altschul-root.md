# Existence and uniqueness of the Karlin–Altschul parameter

Let `p` be a
[probability vector](../../../../ComputerScience/machine-learning/bayesian-inference-and-sampling/expectation-maximization-algorithm/is-dist.md)
on a finite alphabet with `p_a > 0` for every letter `a`, and `s` a real score on pairs of letters
with negative mean, `∑_a ∑_b p_a p_b s(a, b) < 0`, and some positive score, `s(a, b) > 0` for some
`a` and `b`. Then there is exactly one `θ > 0`, the Karlin–Altschul `λ`, with
`∑_{(a, b)} p_a p_b e^{θ s(a, b)} = 1`, that is `E e^{θ s(A, B)} = 1` for independent letters `A`
and `B` of law `p`: the positive root of `m(θ) = 1` for the
[moment generating function](../maximal-segment-score-of-a-random-sequence/score-mgf.md) `m` of the
[pair score](pair-score.md) under the [pair law](pair-law.md) (Karlin and Altschul 1990). The value
`θ = 0` also solves the equation; uniqueness is among positive `θ`.
