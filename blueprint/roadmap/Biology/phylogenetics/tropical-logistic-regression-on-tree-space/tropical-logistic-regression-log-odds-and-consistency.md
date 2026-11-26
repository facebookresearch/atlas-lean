# Tropical logistic regression on tree space: optimal log-odds, consistency and error bounds

**Optimal model.** Let $Y \sim \mathrm{Bernoulli}(r)$ and $X \mid Y \sim f_Y$ on $\mathbb{R}^n$. Then $Y \mid X \sim \mathrm{Bernoulli}\big(S(h(X))\big)$ with $S$ the logistic function and
$$h(x) = \log\frac{r f_1(x)}{(1 - r) f_0(x)},$$
and $p = S \circ h$ maximises the expected log-likelihood. Gaussian classes give classical logistic regression. If the classes are equiprobable tropical Laplace laws on ultrametric trees in $\mathbb{R}^e/\mathbb{R}\mathbf{1}$ with centres $\omega_Y$ and scales $\sigma_Y$, the optimal log-odds are
$$h(x) = \frac{d_{\mathrm{tr}}(x, \omega_0)}{\sigma_0} - \frac{d_{\mathrm{tr}}(x, \omega_1)}{\sigma_1} + (e-1)\log\frac{\sigma_0}{\sigma_1}.$$
The **one-species model** ($\omega_0 = \omega_1 = \omega$, $\sigma_0 < \sigma_1$) classifies by $d_{\mathrm{tr}}(x, \omega) > c$ with $\lambda = \sigma_0^{-1} - \sigma_1^{-1}$ and $\lambda c = (e-1)\log(\sigma_1/\sigma_0)$; the **two-species model** ($\sigma_0 = \sigma_1$) assigns $x$ to the nearer centre.

**Theorem (consistency).** Let $\Omega \subset \mathbb{R}^e/\mathbb{R}\mathbf{1}$ and $\Sigma \subset \mathbb{R}_+$ be compact, let $(X_i, Y_i)$ be i.i.d. with $Y_i \sim \mathrm{Bernoulli}\big(S(h(X_i; \omega^*, \sigma^*))\big)$, and let $d_{\mathrm{tr}}(X, \omega_Y)$ be square-integrable. Then the maximum-likelihood estimator $(\hat\omega, \hat\sigma) \in \Omega^2 \times \Sigma^2$ converges in probability to $(\omega^*, \sigma^*)$.

**Proposition (two-species error bound).** If $X$ has density proportional to $f_Z(d_{\mathrm{tr}}(x, \omega_Y^*))$, $\epsilon = d_{\mathrm{tr}}(\hat\omega_1, \omega_1^*) + d_{\mathrm{tr}}(\hat\omega_0, \omega_0^*)$ and $2\Delta_\epsilon = d_{\mathrm{tr}}(\omega_1^*, \omega_0^*) - \epsilon$, then the misclassification probability is at most $\tfrac12 \bar F_Z(\Delta_\epsilon) + h(\epsilon)$, where $\bar F_Z$ is the complementary distribution function of $Z = d_{\mathrm{tr}}(X, \omega_Y^*)$ and $h$ is increasing with $h(0) = 0$. For tropical Laplace classes and exact parameters this is $\Gamma\big(e-1, d_{\mathrm{tr}}(\omega_0^*, \omega_1^*)/(2\sigma)\big)/\big(2\,\Gamma(e-1)\big)$, with $\Gamma(\cdot,\cdot)$ the upper incomplete gamma function.

## Depends on

- [Tropical Laplace distribution on the space of ultrametric trees](tropical-laplace-distribution-on-the-tropical-projective-torus.md)

## Expansion

The log-odds formula is Bayes' rule; maximising $\int [r f_1 \log p + (1-r) f_0 \log(1-p)]$ pointwise in $p$ gives the same $h$. Substituting the tropical Laplace densities, with normalisers $e!\,\sigma_Y^{e-1}$, yields the displayed $h$, so the model is a scaled tropical analogue of a linear predictor. Consistency follows from the uniform law of large numbers on the compact parameter set (dominated by the integrable tropical distance) plus a unique maximiser of the expected log-likelihood. The error bounds come from the triangle inequality for $d_{\mathrm{tr}}$, which converts parameter error $\epsilon$ into a shift of the decision threshold.

## Sources

- G. Aliatimis, R. Yoshida, B. Boyacı, J. A. Grant, *Tropical logistic regression model on space of phylogenetic trees*, Bull. Math. Biol. 86 (2024), 99 (Lemma 1, Proposition 2, Examples 1–2, Eqs. (8)–(9), Theorem 2, Propositions 5–6, Example 4). <https://doi.org/10.1007/s11538-024-01327-8> (PMCID: PMC11219468)
