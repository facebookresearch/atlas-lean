# Posterior inclusion probability

Posterior inclusion probability from a normalized non-negative prior and variant evidence.
When every evidence value is positive, `PriorWeights.evidence_pos` makes the denominator strictly
positive, and `pip_nonneg` and `sum_pip` prove that these values form a probability distribution.
