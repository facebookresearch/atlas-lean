# Invasion rates and protected polymorphisms for patch-selection strategies

A population lives in $n$ patches. Patch $i$ has intrinsic growth rate $\mu_i$ and strength of intraspecific competition $\kappa_i > 0$, and the patch noise is a Brownian motion with covariance matrix $\Sigma = (\sigma_{ij})$. A **patch-selection strategy** is a probability vector $\alpha \in \Delta_n$, the fraction of time spent in each patch. Write $\langle \alpha,\beta\rangle_\kappa = \sum_i \kappa_i\alpha_i\beta_i$. Two morphs with strategies $\alpha$ and $\beta$ and abundances $X_t, Y_t$ obey

$$

\begin{aligned}
dX_t &= X_t\big(\mu\cdot\alpha - \langle\alpha,\alpha\rangle_\kappa X_t - \langle\alpha,\beta\rangle_\kappa Y_t\big)\,dt + X_t\sqrt{\alpha\cdot\Sigma\alpha}\;dU_t,\\
dY_t &= Y_t\big(\mu\cdot\beta - \langle\alpha,\beta\rangle_\kappa X_t - \langle\beta,\beta\rangle_\kappa Y_t\big)\,dt + Y_t\sqrt{\beta\cdot\Sigma\beta}\;dV_t,
\end{aligned}

$$

where $U,V$ are standard Brownian motions built from the common patch noise. Alone, morph $\alpha$ is a stochastic logistic diffusion that persists with a Gamma stationary law iff $\alpha\cdot(\mu - \Sigma\alpha/2) > 0$.

**Invasion rate.** If $\alpha\cdot(\mu - \Sigma\alpha/2) > 0$, the per-capita growth rate of a rare $\beta$-morph against the resident at stationarity is

$$

\mathcal I(\alpha,\beta) = \beta\cdot\Big(\mu - \frac{\Sigma\beta}{2}\Big) - \frac{\langle\alpha,\beta\rangle_\kappa}{\langle\alpha,\alpha\rangle_\kappa}\;\alpha\cdot\Big(\mu - \frac{\Sigma\alpha}{2}\Big),

$$

and $\mathcal I(\alpha,\beta) = \beta\cdot(\mu - \Sigma\beta/2)$ if the resident goes extinct. Always $\mathcal I(\alpha,\beta) \le \beta\cdot(\mu - \Sigma\beta/2)$, and if the resident persists and $\mathcal I(\alpha,\beta) < 0$ then $\mathcal I(\beta,\alpha) > 0$.

**Theorem.**

1. (Exclusion.) If $\alpha\cdot(\mu - \Sigma\alpha/2) > 0$ and $\mathcal I(\alpha,\beta) < 0$, then for every initial condition $(x,y) \in (0,\infty)^2$ the time-averaged laws $\frac1t\int_0^t P^{(x,y)}\{(X_s,Y_s) \in \cdot\}\,ds$ converge weakly as $t \to \infty$ to $\rho_{\alpha}\otimes\delta_0$, where $\rho_\alpha$ is the resident's stationary law: the $\beta$-morph is displaced.
2. (Protected polymorphism.) If $\mathcal I(\alpha,\beta) > 0$ and $\mathcal I(\beta,\alpha) > 0$, there is a unique stationary distribution $\pi$ on $(0,\infty)^2$, absolutely continuous, and time averages of every bounded measurable function of $(X_t,Y_t)$ converge almost surely to their $\pi$-averages.

## Expansion

The resident alone is the logistic diffusion $dZ = Z(\mu - \kappa Z)dt + \sigma Z dW$ with explicit solution and Gamma stationary density with shape $2\mu/\sigma^2 - 1$ and scale $\sigma^2/(2\kappa)$, so $\mathbb{E}_{\rho}[Z] = (\mu - \sigma^2/2)/\kappa$. A rare invader grows like $\exp(\int(\mu\cdot\beta - \langle\alpha,\beta\rangle_\kappa \bar X_s)\,ds - \tfrac12(\beta\cdot\Sigma\beta)t)$, and the ergodic theorem replaces $\bar X_s$ by its stationary mean, giving $\mathcal I$. The exclusion and coexistence statements follow from comparison with the partially linearized system and from stochastic persistence theory for Kolmogorov SDEs.

## Sources

- Steven N. Evans, Alexandru Hening, Sebastian J. Schreiber, "Protected polymorphisms and evolutionary stability of patch-selection strategies in stochastic environments", arXiv (2014); Journal of Mathematical Biology (2015). Section 2 (Proposition 2.1), Section 3 (Propositions 3.1–3.2, Corollary 3.3), Section 4 (Theorems 4.1–4.2). <https://doi.org/10.48550/arXiv.1404.6759>. Published version: Journal of Mathematical Biology 71(2) (2015), 325–359, <https://doi.org/10.1007/s00285-014-0824-5>; locators above refer to the arXiv version.
