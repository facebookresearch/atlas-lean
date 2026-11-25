# Conditional variances of the compensated Bernoulli increments

Assume `∀ n, StronglyMeasurable (ξ n)`, `iIndepFun ξ P`, `∀ i, IdentDistrib (ξ i) (ξ 0) P P`, `∀ i ω, ξ i ω = 0 ∨ ξ i ω = 1`, `P[ξ 0] = p` and `i < j`.

With
respect to the natural filtration of the counting increments, the conditional variance of
every future increment is the constant `p (1 - p)`. Informally, the predictable quadratic
variation of `compensatedBernoulliStep n p ξ` at time `t` is therefore the deterministic
`p (1 - p) ⌊n t⌋ / n` (no quadratic-variation object is defined here), whose limit is
`tendsto_compensatedBernoulli_predictableQV`.
