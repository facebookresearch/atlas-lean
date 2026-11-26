# Outcome misclassification and selection bias in logistic association studies

Let $D \in \{0,1\}$ be true disease status, $Z$ the predictors of interest, $S \in \{0,1\}$ the indicator of inclusion in the study sample, and $D^*$ an observed phenotype with **perfect specificity**, $P(D^* = 1 \mid D = 0) = 0$, but possibly imperfect sensitivity. Write

$$c(Z) = P(D^* = 1 \mid D = 1, S = 1, Z), \qquad r(Z) = \frac{P(S = 1 \mid D = 1, Z)}{P(S = 1 \mid D = 0, Z)},$$

for the sensitivity as a function of $Z$ and the sampling ratio. Then, with $p(Z) = P(D = 1 \mid Z)$ in the target population,

$$P(D^* = 1 \mid Z, S = 1) = \frac{c(Z)\, r(Z)\, p(Z)}{1 + [r(Z) - 1]\, p(Z)} .$$

If the disease model is logistic, $\operatorname{logit} p(Z) = \theta_0 + \theta_Z Z$, then

$$\log \frac{P(D^* = 1 \mid Z, S = 1)}{c(Z) - P(D^* = 1 \mid Z, S = 1)} = \theta_0 + \theta_Z Z + \log r(Z).$$

This is a generalized linear model with a non-logistic link and an offset $\log r(Z)$. Fitting an ordinary logistic regression of $D^*$ on $Z$ in the sample is therefore biased for $\theta_Z$ unless $c \equiv 1$ and $r$ is constant in $Z$. Given $c(Z)$ and $r(Z)$, $\theta$ is estimated by fitting this model. If $c(Z) \equiv \tilde c$ is constant and selection is ignorable, $\tilde c = P(D^* = 1)/P(D = 1)$, and the uncorrected log-odds ratio $\theta_Z^{uc}$ is approximately rescaled as

$$\theta_Z \approx \theta_Z^{uc}\, \frac{\tilde c\,(1 - P(D^* = 1))}{\tilde c - P(D^* = 1)} .$$

## Expansion

By perfect specificity, $P(D^* = 1 \mid Z, S = 1) = c(Z)\, P(D = 1 \mid Z, S = 1)$. By Bayes' rule, selection multiplies the odds of disease by $r(Z)$, so $P(D = 1 \mid Z, S = 1) = r p / (r p + 1 - p)$, which gives the first identity. Dividing by $c$ and taking odds, $q = rp/(1 + (r-1)p)$ satisfies $q/(1-q) = r\, p/(1-p)$. Taking logarithms gives the link-and-offset form.

## Sources

- L. J. Beesley and B. Mukherjee, *Statistical inference for association studies using electronic health records: handling both selection bias and outcome misclassification*, Biometrics (published online 2020), <https://doi.org/10.1111/biom.13400>, Sections 2–3: Eq. 1 (conceptual model), Eq. 2 (sensitivity and sampling-ratio functions), Eq. 3 (key relationship, proved in the paper's Web Appendix A.1), Eq. 4 (logistic case) and Eq. 5 (constant-sensitivity correction), as read from the authors' preprint version.
