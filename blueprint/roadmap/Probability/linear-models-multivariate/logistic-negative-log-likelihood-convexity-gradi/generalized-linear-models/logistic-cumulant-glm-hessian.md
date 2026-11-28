# Hessian of the logistic GLM log-likelihood

For a design matrix $X$, offset $o$ and coefficients $\beta$, let $\eta = X\beta + o$ and $\sigma$ the logistic function. At unit dispersion, the Hessian of the logistic (Bernoulli) GLM log-likelihood in $\beta$ is

$$-X^\top W X, \qquad W = \operatorname{diag}\bigl(\sigma(\eta_i)(1 - \sigma(\eta_i))\bigr).$$
