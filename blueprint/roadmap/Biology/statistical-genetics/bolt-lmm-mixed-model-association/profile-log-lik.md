# Profile log-likelihood of a SNP effect

Let $(K, \sigma_g^2, \sigma_e^2)$ be [variance components](model.md) on $n$ individuals, let $X$ be a real $n \times p$ matrix, and let $x, y \in \mathbb{R}^n$ (a SNP genotype vector and a phenotype vector). The profile log-likelihood of a SNP effect $\gamma \in \mathbb{R}$ is

$$\ell_{\mathrm{prof}}(\gamma) = \sup_{\beta \in \mathbb{R}^p} \ell(X\beta + \gamma x),$$

where $\ell$ is the [marginal log-likelihood](log-lik.md). The supremum is finite because $\ell(\mu) \le -\frac12(n \log(2\pi) + \log\det V)$ for every $\mu$.
