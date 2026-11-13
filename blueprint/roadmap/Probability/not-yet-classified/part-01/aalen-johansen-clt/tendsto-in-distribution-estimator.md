# Joint central limit theorem with its covariance

Under the hypotheses of
`exists_tendstoInDistribution_estimator`, there is a Gaussian random vector `Y` (on the standard
Gaussian space of the cells) such that `√n · (estimator - ajMap m (cellMean μ)) → Y` in
distribution, and every linear combination `∑ₐ sₐ Yₐ` is centered Gaussian with variance
`Var[∑ₐ sₐ · influence μ m (W 0) a]`. Equivalently, the covariance matrix of `Y` is the covariance
matrix of the influence vector of one subject (`covariance_limit`).
