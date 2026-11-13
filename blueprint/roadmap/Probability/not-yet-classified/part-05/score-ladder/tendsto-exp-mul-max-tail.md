# Tilted renewal limit for ladder tails (abstract form)

For any sub-probability law `g`
on `{1, 2, …}` and any `T` solving `T k = ∑_{j > k} g j + ∑_{j ≤ k} g j * T (k - j)`, if
`θ > 0` satisfies `∑ g j e^{θ j} = 1`, the support of `g` is aperiodic and
`μ = ∑ j g j e^{θ j}` is finite, then `e^{θ k} T k → (1 - ∑ g) / ((e^θ - 1) μ)`. Here `g` and
`T` are arbitrary; the score-walk instance, with `g` the ladder-height law and
`T k = P(M > k)`, is `tendsto_exp_mul_maxTail_scoreWalk`.
