# The log marginal likelihood is not jointly concave

For one zero count at size factor
`1`, `ℓ(a, b) = a log (b / (b + 1))` violates midpoint concavity between `(1, 1)` and `(3, 3)`:
`ℓ(2, 2) < (ℓ(1, 1) + ℓ(3, 3)) / 2`, because `2¹¹ < 3⁷`. Concavity holds only in each
hyperparameter separately (`concaveOn_logMarginalLik_shape`,
`strictConcaveOn_logMarginalLik_logRate`).
