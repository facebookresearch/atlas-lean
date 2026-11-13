# The full covariance matrix of the joint limit

If `Y` is a limit vector as in
`tendstoInDistribution_estimator`, i.e. every linear combination `∑ₐ sₐ Yₐ` is centered Gaussian
with variance `Var[∑ₐ sₐ · influence μ m (W 0) a]`, then for all coordinates `a, b`,
`Cov(Yₐ, Y_b) = Cov(influenceₐ, influence_b)` under the subject law: the asymptotic covariance of
the joint Kaplan–Meier and Aalen–Johansen estimator is the covariance of the influence vector.
