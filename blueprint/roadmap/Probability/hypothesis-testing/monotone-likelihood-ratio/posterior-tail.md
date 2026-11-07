# Posterior tail probability

Posterior probability of `{θ > t}` after observing `n`, by Bayes' formula for the prior
`μ` and likelihood `L`: `(∫_{θ > t} L n θ dμ) / ∫ L n θ dμ`. Meaningful when the marginal
likelihood `∫ L n dμ` is positive (otherwise the division returns the junk value `0`), and a
genuine posterior probability only when `L` is nonnegative (as in the MLR predicates:
a signed `L` can give a value outside `[0, 1]`).
