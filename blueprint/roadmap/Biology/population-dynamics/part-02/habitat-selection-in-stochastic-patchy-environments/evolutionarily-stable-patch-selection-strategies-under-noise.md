# Evolutionarily stable patch-selection strategies under environmental noise

In the stochastic patch model with growth rates $\mu \in \mathbb{R}^n$, carrying-capacity parameters $\kappa_i > 0$, noise covariance $\Sigma = (\sigma_{ij})$, and invasion rate

$$

\mathcal I(\alpha,\beta) = \beta\cdot\Big(\mu - \frac{\Sigma\beta}{2}\Big) - \frac{\langle\alpha,\beta\rangle_\kappa}{\langle\alpha,\alpha\rangle_\kappa}\;\alpha\cdot\Big(\mu - \frac{\Sigma\alpha}{2}\Big), \qquad \langle\alpha,\beta\rangle_\kappa = \sum_i \frac{\alpha_i\beta_i}{\kappa_i},

$$

a strategy $\alpha \in \Delta_n$ is an **evolutionarily stable strategy (ESS)** if it persists ($\alpha\cdot(\mu - \Sigma\alpha/2) > 0$) and $\mathcal I(\alpha,\beta) < 0$ for every $\beta \ne \alpha$.

**Theorem.** Assume $\Sigma$ is positive definite and $\max_\alpha \alpha\cdot(\mu - \Sigma\alpha/2) > 0$.

1. (Mixed ESS.) An ESS $\alpha$ with support $I \subseteq \{1,\dots,n\}$, $|I| \ge 2$, satisfies for all $i \in I$

$$

-\frac{\alpha\cdot\Sigma\alpha}{2} = \mu_i - \kappa_i\,\alpha_i\,\frac{\alpha\cdot(2\mu - \Sigma\alpha)}{2\langle\alpha,\alpha\rangle_\kappa} - \sum_{j=1}^n \sigma_{ij}\alpha_j .

$$

Conversely, if $I = \{1,\dots,n\}$, every strategy satisfying these equations is an ESS.

2. (Pure ESS.) Using only patch $i$ is an ESS iff, for every $j \ne i$,

$$

\mu_j - \frac{\sigma_{jj}}{2} < -\frac{\sigma_{jj}}{2} + \sigma_{ij} - \frac{\sigma_{ii}}{2}.

$$

3. (Two patches.) For $n = 2$, a mixed ESS exists whenever the reverse strict inequalities hold for both $i = 1,2$ ($j \ne i$).

Compared with the deterministic ideal free distribution ($\alpha_i \propto \kappa_i$ restricted to source patches), noise makes the ESS spend less time in patches with large carrying capacity and can make it use sink patches with $\mu_i < 0$: spatial bet hedging.

## Expansion

For fixed resident $\alpha$, $\beta \mapsto \mathcal I(\alpha,\beta)$ is a strictly concave quadratic on the simplex vanishing at $\beta = \alpha$. So $\alpha$ is an ESS iff it is the strict maximizer of this function over $\Delta_n$, and the Karush–Kuhn–Tucker conditions give the equations on the support (equality of the gradient across used patches) and inequalities off the support. Positive definiteness of $\Sigma$ gives the strict concavity, which makes the KKT conditions sufficient when all patches are used. For a single-patch strategy the gradient condition reduces to the stated pairwise inequalities.

## Sources

- Steven N. Evans, Alexandru Hening, Sebastian J. Schreiber, "Protected polymorphisms and evolutionary stability of patch-selection strategies in stochastic environments", arXiv (2014); Journal of Mathematical Biology (2015). Section 5 (Theorem 5.1). <https://doi.org/10.48550/arXiv.1404.6759>. Published version: Journal of Mathematical Biology 71(2) (2015), 325–359, <https://doi.org/10.1007/s00285-014-0824-5>; locators above refer to the arXiv version.
