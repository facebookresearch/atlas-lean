# Analytic Bayes factor for simultaneous multivariate linear regressions

**Model.** A system of simultaneous multivariate linear regressions (SSMR) describes $s$ non-overlapping subgroups (e.g. cohorts in a meta-analysis), each with $n_i$ subjects and the same $r$ responses (e.g. expression in $r$ tissues) and $p$ explanatory variables of interest (genotypes):

$$Y_i = X_{c,i} B_{c,i} + X_{g,i} B_{g,i} + E_i, \qquad E_i \sim \mathrm{MN}(0, I, \Sigma_i), \qquad i = 1, \dots, s,$$

with controlled covariates $X_{c,i}$ (including the intercept) and independent errors across subgroups. Special cases are multiple regression ($s = r = 1$), multivariate regression ($s = 1$; multi-tissue eQTL mapping) and systems of simultaneous linear regressions ($r = 1$; meta-analytic fine-mapping). Stack the genetic effects into $\beta_g = (\mathrm{vec}(B_{g,1}'), \dots, \mathrm{vec}(B_{g,s}'))$ with prior $\beta_g \sim \mathcal{N}(0, W_g)$, give the controlled coefficients a normal prior whose precision tends to zero, and let $\hat\beta_g$ be the maximum likelihood estimate with variance $V_g = \operatorname{Var}(\hat\beta_g)$. The Bayes factor of the model with prior covariance $W_g$ against $H_0: \beta_g = 0$ is the limit of the marginal-likelihood ratio as the controlled-coefficient prior becomes flat; for singular $W_g$ it is defined as the limit of the Bayes factors for $W_g + \lambda I$ as $\lambda \to 0$, which always exists.

**Lemma (known error variances).** If all $\Sigma_i$ are known,

$$\mathrm{BF}(W_g) = \big|I + V_g^{-1}W_g\big|^{-1/2} \exp\Big(\frac12\, \hat\beta_g' V_g^{-1}\big[W_g (I + V_g^{-1}W_g)^{-1}\big] V_g^{-1}\hat\beta_g\Big).$$

**Proposition (unknown error variances).** With inverse-Wishart priors $\Sigma_i \sim \mathrm{IW}(\nu_i, H_i)$, Laplace's method gives the approximation $\mathrm{ABF}(W_g, \alpha)$ obtained by substituting into the same formula, in $V_g$ and (when it depends on them) $W_g$, the shrinkage estimates

$$\check\Sigma_i = \frac{\nu_i}{n_i + \nu_i} H_i + \frac{n_i}{n_i + \nu_i}\big[\alpha_i \hat\Sigma_i + (1 - \alpha_i)\tilde\Sigma_i\big],$$

where $\hat\Sigma_i$, $\tilde\Sigma_i$ are the residual MLEs under the alternative and null models and $\alpha_i \in [0,1]$. Then

$$\mathrm{BF}(W_g) = \mathrm{ABF}(W_g, \alpha) \prod_{i=1}^s \big(1 + O(n_i^{-1})\big).$$

## Expansion

With the controlled covariates profiled out under a flat prior, the likelihood depends on $\beta_g$ only through the Gaussian kernel of $\hat\beta_g \sim \mathcal{N}(\beta_g, V_g)$; integrating against $\mathcal{N}(0, W_g)$ gives the ratio of $\mathcal{N}(0, V_g + W_g)$ to $\mathcal{N}(0, V_g)$ densities at $\hat\beta_g$, which is the stated formula. The exponent is half a weighted Wald-type statistic, connecting the Bayes factor to frequentist tests and to the BIC. Choosing $W_g$ with structured zeros or rank deficiencies encodes which tissues or cohorts carry an effect, so model selection over configurations $\xi(\beta_g)$ reduces to comparing closed-form Bayes factors, e.g. for tissue-specific eQTL mapping.

## Sources

- X. Wen, "Bayesian model selection in complex linear systems, as illustrated in genetic association studies", *Biometrics* 70 (2014), 73–83, <https://doi.org/10.1111/biom.12112>; preprint arXiv:1309.0837 (2013), Section 2 (SSMR model), Section 4.1 (Definitions 1–2, Lemma 1, Propositions 1–2), Section 4.2 (connections to frequentist statistics), <https://doi.org/10.48550/arXiv.1309.0837>.
