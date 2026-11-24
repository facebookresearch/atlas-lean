# Covariance sq le variance mul variance

Cauchy--Schwarz for the finite-state covariance: `(Cov_P(X, Y)) ^ 2 ≤ Var_P(X) * Var_P(Y)`
when the weights are nonnegative. From `Finset.sum_mul_sq_le_sq_mul_sq` with `√P` weights
on the centered variables; it is the key step of the Hansen--Jagannathan bound.
