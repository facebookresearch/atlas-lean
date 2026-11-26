# Latent variance component REML

Gene expression data carry correlation from known confounders (batch, sex, cell composition) and unknown ones. Modelling both as random effects with a shared covariance gives a restricted maximum-likelihood problem whose solution is closed-form: latent factors are leading eigenvectors of the sample covariance projected away from the known covariates, with the residual variance given by the remaining eigenvalues.

- [Closed-form restricted maximum likelihood for latent variance components](closed-form-restricted-maximum-likelihood-for-latent-variance-components.md)
