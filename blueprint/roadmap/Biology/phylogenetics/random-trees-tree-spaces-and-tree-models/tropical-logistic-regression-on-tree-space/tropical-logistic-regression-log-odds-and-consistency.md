# Tropical logistic regression on tree space: optimal log-odds, consistency and error bounds

**Optimal model.** Let $Y \sim \mathrm{Bernoulli}(r)$ and $X \mid Y \sim f_Y$ on $\mathbb{R}^n$. Then $Y \mid X \sim \mathrm{Bernoulli}\big(S(h(X))\big)$ with $S$ the logistic function and

$$h(x) = \log\frac{r f_1(x)}{(1 - r) f_0(x)},$$

and $p = S \circ h$ maximises the expected log-likelihood. Gaussian classes $N(\omega_Y, \Sigma)$ with a common nonsingular covariance $\Sigma$ (in the source, $\sigma^2 I$) give affine log-odds, i.e. classical logistic regression; unequal covariances give quadratic log-odds in general (equal priors with $N(0,1)$ and $N(0,4)$ give $h(x) = -\log 2 + 3x^2/8$). If the classes are equiprobable tropical Laplace laws with centres $\omega_Y$ and scales $\sigma_Y$, densities with respect to Lebesgue measure on the whole tropical projective torus $\mathbb{R}^e/\mathbb{R}\mathbf{1}$ (an ambient law: ultrametric trees are points at which the classifier is evaluated, not the support of the law), the optimal log-odds are

$$h(x) = \frac{d_{\mathrm{tr}}(x, \omega_0)}{\sigma_0} - \frac{d_{\mathrm{tr}}(x, \omega_1)}{\sigma_1} + (e-1)\log\frac{\sigma_0}{\sigma_1}.$$

The **one-species model** ($\omega_0 = \omega_1 = \omega$, $\sigma_0 < \sigma_1$) classifies by $d_{\mathrm{tr}}(x, \omega) > c$ with $\lambda = \sigma_0^{-1} - \sigma_1^{-1}$ and $\lambda c = (e-1)\log(\sigma_1/\sigma_0)$; the **two-species model** ($\sigma_0 = \sigma_1$) assigns $x$ to the nearer centre.

**Theorem (consistency).** Let $\Omega \subset \mathbb{R}^e/\mathbb{R}\mathbf{1}$ and $\Sigma \subset \mathbb{R}_+$ be compact, let $(X_i, Y_i)$ be i.i.d. with $Y_i \mid X_i \sim \mathrm{Bernoulli}\big(S(h(X_i; \omega^*, \sigma^*))\big)$ for a true parameter $(\omega^*, \sigma^*) = (\omega_0^*, \omega_1^*, \sigma_0^*, \sigma_1^*) \in \Omega^2 \times \Sigma^2$, and let $d_{\mathrm{tr}}(X, \omega)$ be square-integrable for $\omega \in \Omega$. Assume the identification conditions under which the source's proof applies its Lemma 2: the two true centre–scale pairs differ, $(\omega_0^*, \sigma_0^*) \ne (\omega_1^*, \sigma_1^*)$, and the support of the covariate $X$ contains a neighbourhood of every point of $\Omega$, so of the two true centres and of both centres of every competing parameter (the source's proof takes $X$ with positive density everywhere). Then the maximum-likelihood estimator $(\hat\omega, \hat\sigma) \in \Omega^2 \times \Sigma^2$ converges in probability to $(\omega^*, \sigma^*)$. Without the first condition the parameter is not identifiable: with equal centres and equal scales the log-odds vanish identically for every common centre and scale.

**Proposition (two-species error bound).** If $X$ has density proportional to $f_Z(d_{\mathrm{tr}}(x, \omega_Y^*))$, $\epsilon = d_{\mathrm{tr}}(\hat\omega_1, \omega_1^*) + d_{\mathrm{tr}}(\hat\omega_0, \omega_0^*)$ and $2\Delta_\epsilon = d_{\mathrm{tr}}(\omega_1^*, \omega_0^*) - \epsilon$, and ties have probability zero, $P\big(d_{\mathrm{tr}}(X, \omega_1^*) = d_{\mathrm{tr}}(X, \omega_0^*)\big) = 0$ (tropical bisectors can have positive measure), then the misclassification probability is at most $\tfrac12 \bar F_Z(\Delta_\epsilon) + h(\epsilon)$, where $\bar F_Z$ is the complementary distribution function of $Z = d_{\mathrm{tr}}(X, \omega_Y^*)$ and $h$ is increasing with $h(0) = 0$ and $2h(\epsilon) \le \bar F_Z(\Delta_\epsilon)$. For ambient tropical Laplace classes with a common scale $\sigma$ and exact parameters this is $\Gamma\big(e-1, d_{\mathrm{tr}}(\omega_0^*, \omega_1^*)/(2\sigma)\big)/\big(2\,\Gamma(e-1)\big)$, with $\Gamma(\cdot,\cdot)$ the upper incomplete gamma function.

## Depends on

- [Tropical Laplace distribution on the tropical projective torus](tropical-laplace-distribution-on-the-tropical-projective-torus.md)

## Expansion

The log-odds formula is Bayes' rule; maximising $\int [r f_1 \log p + (1-r) f_0 \log(1-p)]$ pointwise in $p$ gives the same $h$. Substituting the ambient tropical Laplace densities, with normalisers $e!\,\sigma_Y^{e-1}$ computed by integrating over the whole torus, yields the displayed $h$, so the model is a scaled tropical analogue of a linear predictor. Consistency follows from the uniform law of large numbers on the compact parameter set (dominated by the integrable tropical distance) plus a unique maximiser of the expected log-likelihood, which is where the identification conditions enter: a competing maximiser must give the same log-odds as the true parameter on the support of $X$, and Lemma 2 of the source shows that two parameters whose log-odds agree on a set containing neighbourhoods of all four centres, the two true ones and the two competing ones, coincide when the true centre–scale pairs differ. Neighbourhoods of the true centres alone do not suffice for this argument, since a competing centre in $\Omega$ may lie outside them. The error bounds come from the triangle inequality for $d_{\mathrm{tr}}$, which converts parameter error $\epsilon$ into a shift of the decision threshold.

## Sources

- G. Aliatimis, R. Yoshida, B. Boyacı, J. A. Grant, *Tropical logistic regression model on space of phylogenetic trees*, Bull. Math. Biol. 86 (2024), 99 (Lemma 1, Proposition 2, Examples 1–2, Eqs. (8)–(9), Theorem 2, Propositions 5–6, Example 4). <https://doi.org/10.1007/s11538-024-01327-8> (PMCID: PMC11219468)
