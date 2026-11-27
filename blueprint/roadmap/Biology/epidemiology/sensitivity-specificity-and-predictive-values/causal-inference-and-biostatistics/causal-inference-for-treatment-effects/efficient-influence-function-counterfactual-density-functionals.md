# Efficient influence functions for counterfactual density functionals

Use the notation of [the counterfactual density projection](counterfactual-density-projection-moment-condition.md): $Z = (X, A, Y) \sim P$, propensity $\pi_a(x)$, conditional density $\eta_a(y \mid x)$ and adjusted density $p_a(y) = \int \eta_a(y \mid x)\,dP(x)$. For a random variable $T$ define the map (eq. 15)

$$\varphi_a(T; P) = \frac{\mathbb{1}(A = a)}{\pi_a(X)}\{T - E(T \mid X, A = a)\} + E(T \mid X, A = a) - E\{E(T \mid X, A = a)\},$$

the efficient influence function of $E\{E(T \mid X, A = a)\}$.

**Lemma 1 (von Mises expansion).** Let $\psi(P) = \int h\{p_a(y)\}\,dy$ for a twice continuously differentiable $h$. For any second distribution $\bar P$ (with nuisances $\bar\pi_a, \bar\eta_a, \bar p_a$, and $\bar\pi_a > 0$), with all integrals below finite,

$$\psi(\bar P) - \psi(P) = \int \varphi_a\{h'(\bar p_a(Y)); \bar P\}\,d(\bar P - P) + R_2(\bar P, P),$$

where the remainder is second order,

$$R_2(\bar P, P) = \iint h'\{\bar p_a(y)\}\Big\{\frac{\pi_a(x)}{\bar\pi_a(x)} - 1\Big\}\{\eta_a(y \mid x) - \bar\eta_a(y \mid x)\}\,dy\,dP(x) - \frac12\int h''\{p_a^*(y)\}\{\bar p_a(y) - p_a(y)\}^2\,dy,$$

with $p_a^*(y)$ between $p_a(y)$ and $\bar p_a(y)$. The curvature term enters with a minus sign: with no covariates, unchanged propensity and $h(u) = u^2$, the left side minus the linear term is $\int\{\bar p_a^2 - p_a^2 - 2\bar p_a(\bar p_a - p_a)\} = -\int(\bar p_a - p_a)^2$. Hence $\psi$ is pathwise differentiable with efficient influence function $\varphi_a\{h'(p_a(Y)); P\}$.

**Theorem 1.** Assume $f$ is twice differentiable. In the nonparametric model, the efficient influence function of the moment $m(\beta)$ of Proposition 1 at fixed $\beta$ is $\varphi_a\{\gamma_f(Y;\beta)\}$, where

$$\gamma_f(y;\beta) = \frac{\partial g(y;\beta)}{\partial\beta}\Big[f_1'\{p_a(y), g(y;\beta)\} + g(y;\beta)\,f_{21}''\{p_a(y), g(y;\beta)\}\Big].$$

If moreover the Jacobian $\partial m(\beta)/\partial\beta$ at $\beta_0$ is nonsingular (uniqueness of the minimizer does not imply this: a normal location family with mean $\beta^3$ has a unique KL projection of a standard normal target at $\beta_0 = 0$, where the Jacobian vanishes), the efficient influence functions of $\beta_0$ and of $g(y;\beta_0)$ are

$$-\Big(\frac{\partial m(\beta)}{\partial\beta}\Big|_{\beta_0}\Big)^{-1}\varphi_a\{\gamma_f(Y;\beta_0)\} \quad\text{and}\quad -\frac{\partial g(y;\beta)}{\partial\beta^{\top}}\Big(\frac{\partial m(\beta)}{\partial\beta}\Big|_{\beta_0}\Big)^{-1}\varphi_a\{\gamma_f(Y;\beta_0)\}. \qquad\text{(eq. 17)}$$

**Corollary 4.** $\gamma_f = -2\,\partial g/\partial\beta$ for $D_f = L_2^2$ and $\gamma_f = -\partial\log g/\partial\beta$ for KL. For the $L_2^2$ projection onto a truncated series and the KL projection onto an exponential family, the efficient influence function of $m(\beta)$ is proportional to $\varphi_a\{b(Y)\}$, with constants $-2$ and $-1$ respectively.

## Expansion

The first remainder term is a product of the propensity error and the outcome-density error, so a one-step estimator $\psi(\hat P) + P_n\varphi_a\{h'(\hat p_a(Y)); \hat P\}$ built from cross-fitted nuisances is root-$n$ consistent and efficient whenever the estimated remainder $R_2(\hat P, P)$ is $o_P(n^{-1/2})$, which the product structure makes possible with nuisance estimators converging at slower than parametric rates. Theorem 1 then follows by applying Lemma 1 to each component of $m(\beta)$, whose integrand is a smooth function of $p_a(y)$, and, when $\partial m/\partial\beta$ is nonsingular at $\beta_0$, the implicit function theorem and the delta method give $\beta_0$ and $g(\cdot;\beta_0)$. The efficiency bound grows when $g$ or $f$ is sensitive to small changes, since $\gamma_f$ involves their derivatives.

## Depends on

- [Counterfactual density and its projection onto a model by a moment condition](counterfactual-density-projection-moment-condition.md)

## Sources

- E. H. Kennedy, S. Balakrishnan and L. Wasserman, *Semiparametric counterfactual density estimation*, Biometrika (2023). <https://doi.org/10.1093/biomet/asad017>
