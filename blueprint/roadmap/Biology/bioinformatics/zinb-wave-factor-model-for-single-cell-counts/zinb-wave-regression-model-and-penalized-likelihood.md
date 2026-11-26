# ZINB-WaVE regression model and penalized likelihood

**Distributions.** For $\mu \ge 0$ and $\theta > 0$ the negative binomial probability mass function with mean $\mu$ and inverse dispersion $\theta$ is

$$f_{NB}(y;\mu,\theta) = \frac{\Gamma(y+\theta)}{\Gamma(y+1)\Gamma(\theta)}\Big(\frac{\theta}{\theta+\mu}\Big)^{\theta}\Big(\frac{\mu}{\mu+\theta}\Big)^{y}, \qquad y \in \mathbb{N},$$

with variance $\mu + \mu^2/\theta$; it reduces to the Poisson law as $\theta \to \infty$. For $\pi \in [0,1]$ the zero-inflated negative binomial (ZINB) law is

$$f_{ZINB}(y;\mu,\theta,\pi) = \pi\,\delta_0(y) + (1-\pi) f_{NB}(y;\mu,\theta),$$

where $\pi$ is the probability that a zero (a dropout) is observed in place of the actual count.

**Model.** Let $Y_{ij}$ be the count of gene $j \in \{1,\dots,J\}$ in cell $i \in \{1,\dots,n\}$, modelled as independent ZINB variables with parameters $\mu_{ij}, \theta_{ij}, \pi_{ij}$ satisfying

$$\ln \mu = X\beta_\mu + (V\gamma_\mu)^\top + W\alpha_\mu + O_\mu, \qquad \operatorname{logit}\pi = X\beta_\pi + (V\gamma_\pi)^\top + W\alpha_\pi + O_\pi, \qquad \ln\theta_{ij} = \zeta_j .$$

Here $X$ is a known $n \times M$ matrix of cell-level covariates with $M \times J$ coefficient matrices $\beta = (\beta_\mu,\beta_\pi)$; $V$ is a known $J \times L$ matrix of gene-level covariates with $L \times n$ coefficient matrices $\gamma = (\gamma_\mu,\gamma_\pi)$; $W$ is an unobserved $n \times K$ matrix of latent cell-level factors with $K \times J$ loadings $\alpha = (\alpha_\mu,\alpha_\pi)$; $O_\mu, O_\pi$ are known offsets; and $\zeta \in \mathbb{R}^J$ are gene-wise log inverse dispersions. A column of ones in $X$ gives gene-specific intercepts (baseline expression), and a column of ones in $V$ gives cell-specific intercepts, which act as global-scaling (library-size) normalization factors; the decomposition $1_n\beta_1 + (1_J\gamma_1)^\top$ is unique only up to an additive constant.

**Estimator.** With log-likelihood $\ell(\beta,\gamma,W,\alpha,\zeta) = \sum_{i,j}\ln f_{ZINB}(Y_{ij};\mu_{ij},\theta_{ij},\pi_{ij})$, the parameters are estimated by maximizing $\ell - \mathrm{Pen}$ with

$$\mathrm{Pen} = \frac{\epsilon_\beta}{2}\|\beta^0\|^2 + \frac{\epsilon_\gamma}{2}\|\gamma^0\|^2 + \frac{\epsilon_W}{2}\|W\|^2 + \frac{\epsilon_\alpha}{2}\|\alpha\|^2 + \frac{\epsilon_\zeta}{2}\operatorname{Var}(\zeta),$$

where $\|\cdot\|$ is the Frobenius norm, $\beta^0,\gamma^0$ exclude the unpenalized intercept rows, and $\operatorname{Var}(\zeta)$ is the sample variance of the entries of $\zeta$, so dispersions are shrunk toward a common value rather than toward $0$. The balanced default is $\epsilon_\beta = \epsilon_\alpha = \epsilon/J$, $\epsilon_\gamma = \epsilon_W = \epsilon/n$, $\epsilon_\zeta = \epsilon$. The penalized likelihood is not concave, so only a local maximum is computed; the optimization keeps $W$ and $\alpha^\top$ with orthogonal columns by re-splitting $W\alpha$ through its singular value decomposition.

## Expansion

Because $Y_{ij}$ is modelled on raw counts, the cell intercept in the $\mu$-regression plays the role of a size factor and no preliminary normalization is needed. Separating the regressions for $\mu$ and $\pi$ allows known factors (batch, detection rate) to act on the mean, on the dropout probability or on both. The likelihood depends on $(W,\alpha)$ only through $R = W\alpha$, which is why the factor penalty can be rewritten as a penalty on $R$. Estimation alternates between dispersion updates, ridge-penalized logistic/negative-binomial regressions for the left factors $(\gamma, W)$ and for the right factors $(\beta,\alpha)$, and an orthogonalization step obtained from an SVD of the current $\hat W\hat\alpha$.

## Sources

- D. Risso, F. Perraudeau, S. Gribkova, S. Dudoit, J.-P. Vert, "A general and flexible method for signal extraction from single-cell RNA-seq data", Nature Communications 9 (2018) 284, Methods ("ZINB-WaVE model", Eqs. (1)–(5), and "ZINB-WaVE estimation procedure"), <https://doi.org/10.1038/s41467-017-02554-5>, PMCID PMC5773593.
