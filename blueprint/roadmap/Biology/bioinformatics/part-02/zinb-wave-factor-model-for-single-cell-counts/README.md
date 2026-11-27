# ZINB-WaVE factor model for single-cell counts

The ZINB-WaVE model treats each entry of a cells-by-genes count matrix as a zero-inflated negative binomial variable whose log-mean and logit dropout probability are linear in known cell-level covariates, known gene-level covariates and a low-rank matrix of unobserved cell-level factors. The factors are estimated by penalized maximum likelihood, and the quadratic penalty on the factor matrices is equivalent to a nuclear-norm penalty on their product.

- [ZINB-WaVE regression model and penalized likelihood](zinb-wave-regression-model-and-penalized-likelihood.md)
- [Nuclear-norm form of the ZINB-WaVE factor penalty](nuclear-norm-form-of-the-zinb-wave-factor-penalty.md)
