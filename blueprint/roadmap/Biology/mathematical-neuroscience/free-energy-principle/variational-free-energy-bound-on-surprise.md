# Variational free energy as an upper bound on surprise

**Setting.** A generative model $m$ specifies a joint density $p(y, u \mid m) = p(y \mid u, m)\, p(u \mid m)$ of sensory data $y$ and hidden causes $u$ (hidden and causal states at all levels of a hierarchy). The model evidence is $p(y \mid m) = \int p(y, u \mid m)\, du$ and the **surprise** of the data is $-\ln p(y \mid m)$. Assume the evidence is positive and finite, $0 < p(y \mid m) < \infty$, so that the posterior $p(u \mid y, m) = p(y, u \mid m)/p(y \mid m)$ is a probability density. For a probability density $q(u)$ (the recognition or ensemble density) with $q \ll p(\cdot \mid y, m)$ define the **variational free energy** by the log-ratio integral

$$F(q, y) = \int q(u)\, \ln \frac{q(u)}{p(y, u \mid m)}\, du \in (-\infty, +\infty] .$$

When the energy $U = -\langle \ln p(y \mid u, m) + \ln p(u \mid m) \rangle_q$ and the entropy $S = -\langle \ln q(u) \rangle_q$ are both finite, $F(q, y) = U - S$; without that assumption $U - S$ can be $\infty - \infty$, while the log-ratio integral is still defined.

**Theorem.** For every probability density $q$ with $q \ll p(\cdot \mid y, m)$,

$$F(q, y) = -\ln p(y \mid m) + D_{\mathrm{KL}}\big(q(u) \,\|\, p(u \mid y, m)\big) \ \ge\ -\ln p(y \mid m),$$

with equality if and only if $q(u) = p(u \mid y, m)$ almost everywhere. Hence minimizing $F$ over $q$ (within a parametric family $q(u \mid \lambda)$, by gradient flow $\dot\lambda \propto -\partial F/\partial\lambda$ in the variational parameters) simultaneously (i) tightens an upper bound on surprise and (ii) makes $q$ approximate the posterior; under a Gaussian (Laplace) family $q(u \mid \lambda) = \mathcal{N}(\mu, \Sigma)$ the sufficient statistics $\lambda = \{\mu, \Sigma\}$ are the conditional mean and covariance of the causes.

## Expansion

Write $p(y, u \mid m) = p(u \mid y, m)\, p(y \mid m)$ inside the logarithm: the integrand becomes $q \ln (q/p(u \mid y, m)) - q \ln p(y \mid m)$, and the second term integrates to the finite constant $-\ln p(y \mid m)$ because $q$ is a probability density and the evidence is positive and finite. The first term integrates to the Kullback–Leibler divergence, which is well defined in $[0, \infty]$ for $q \ll p(\cdot \mid y, m)$; this is the stated identity. Nonnegativity of the divergence (Gibbs' inequality, a consequence of Jensen's inequality) gives the bound and its equality case. The finiteness caveat on $U - S$ is real: with evidence $1$ and prior, posterior and $q$ all equal to the density $1/(u (\ln u)^2)$ on $[e, \infty)$, the divergence is $0$ but $U = S = +\infty$. The same quantity is the negative of the evidence lower bound used in variational inference. In hierarchical models of perception, the gradient of $F$ for Gaussian likelihoods and priors is a sum of precision-weighted prediction errors, $\varepsilon^{(i)} = v^{(i)} - g(x^{(i+1)}, v^{(i+1)})$, between the causes at one level and their predictions from the level above; minimizing $F$ then amounts to message passing in which predictions descend and prediction errors ascend the hierarchy, which is the computational reading of predictive coding in cortex.

## Sources

- Kiebel SJ, Daunizeau J, Friston KJ, "A hierarchy of time-scales and the brain" (2008), Methods, "Variational Inversion" (Equations (3)–(5)), <https://doi.org/10.1371/journal.pcbi.1000209>, PMCID PMC2568860.
- K. Friston, "Hierarchical models in the brain", PLoS Computational Biology 4 (2008) e1000211, <https://doi.org/10.1371/journal.pcbi.1000211>.
