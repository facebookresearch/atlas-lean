# Variational free energy as an upper bound on surprise

**Setting.** A generative model $m$ specifies a joint density $p(y, u \mid m) = p(y \mid u, m)\, p(u \mid m)$ of sensory data $y$ and hidden causes $u$ (hidden and causal states at all levels of a hierarchy). The model evidence is $p(y \mid m) = \int p(y, u \mid m)\, du$ and the **surprise** of the data is $-\ln p(y \mid m)$. For any probability density $q(u)$ (the recognition or ensemble density) define the **variational free energy**

$$F(q, y) = U - S, \qquad U = -\big\langle \ln p(y \mid u, m) + \ln p(u \mid m) \big\rangle_q, \qquad S = -\langle \ln q(u) \rangle_q .$$

**Theorem.** For every $q$ with $q \ll p(\cdot \mid y, m)$,

$$F(q, y) = -\ln p(y \mid m) + D_{\mathrm{KL}}\big(q(u) \,\|\, p(u \mid y, m)\big) \ \ge\ -\ln p(y \mid m),$$

with equality if and only if $q(u) = p(u \mid y, m)$ almost everywhere. Hence minimizing $F$ over $q$ (within a parametric family $q(u \mid \lambda)$, by gradient flow $\dot\lambda \propto -\partial F/\partial\lambda$ in the variational parameters) simultaneously (i) tightens an upper bound on surprise and (ii) makes $q$ approximate the posterior; under a Gaussian (Laplace) family $q(u \mid \lambda) = \mathcal{N}(\mu, \Sigma)$ the sufficient statistics $\lambda = \{\mu, \Sigma\}$ are the conditional mean and covariance of the causes.

## Expansion

Write $p(y, u \mid m) = p(u \mid y, m)\, p(y \mid m)$ inside $U$: then $U - S = \langle \ln q(u) - \ln p(u \mid y, m)\rangle_q - \ln p(y \mid m)$, which is the stated identity. Nonnegativity of the Kullback–Leibler divergence (Gibbs' inequality, a consequence of Jensen's inequality) gives the bound and its equality case. The same quantity is the negative of the evidence lower bound used in variational inference. In hierarchical models of perception, the gradient of $F$ for Gaussian likelihoods and priors is a sum of precision-weighted prediction errors, $\varepsilon^{(i)} = v^{(i)} - g(x^{(i+1)}, v^{(i+1)})$, between the causes at one level and their predictions from the level above; minimizing $F$ then amounts to message passing in which predictions descend and prediction errors ascend the hierarchy, which is the computational reading of predictive coding in cortex.

## Sources

- Kiebel SJ, Daunizeau J, Friston KJ, "A hierarchy of time-scales and the brain" (2008), Methods, "Variational Inversion" (Equations (3)–(5)), <https://doi.org/10.1371/journal.pcbi.1000209>, PMCID PMC2568860.
- K. Friston, "Hierarchical models in the brain", PLoS Computational Biology 4 (2008) e1000211, <https://doi.org/10.1371/journal.pcbi.1000211>.
