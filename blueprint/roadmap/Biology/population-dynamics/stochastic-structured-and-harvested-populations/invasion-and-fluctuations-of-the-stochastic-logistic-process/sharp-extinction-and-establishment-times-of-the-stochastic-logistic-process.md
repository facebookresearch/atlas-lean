# Sharp extinction and establishment times of the stochastic logistic process

Let $X^{(n)}$ be the [stochastic logistic process](invasion-probability-and-potential-barrier-of-the-stochastic-logistic-process.md) with per-capita rates $\lambda(i/n)$, $\mu(i/n)$, carrying capacity $\kappa$ and potential $V(\iota) = \int_0^\iota \ln(\mu(x)/\lambda(x))\,dx$, and assume moreover that $\lambda$ and $\mu$ are differentiable at $\kappa$ with $\frac{\mu'(\kappa)}{\mu(\kappa)} - \frac{\lambda'(\kappa)}{\lambda(\kappa)} > 0$. Write $\rho = \mu(0)/\lambda(0) < 1$ and fix an initial size $m \ge 1$.

**Theorem.** As $n \to \infty$:

1. The expected extinction time is exponentially large in $n$ with a Gaussian prefactor: there is a constant $c(\lambda,\mu) > 0$, given explicitly in the source, such that

$$
\mathbb{E}_m[T_0] \sim c(\lambda,\mu)\, \frac{1-\rho^m}{1-\rho}\, \sqrt{\frac{2\pi}{n\big(\frac{\mu'(\kappa)}{\mu(\kappa)} - \frac{\lambda'(\kappa)}{\lambda(\kappa)}\big)}}\; \frac{e^{-nV(\kappa)}}{\mu(\kappa)\,\kappa} ,
$$

where $-V(\kappa) > 0$ is the depth of the potential well at carrying capacity; the dependence on the initial size $m$ enters only through the survival probability $1-\rho^m$ of the early branching phase.
2. Conditioned on reaching carrying capacity before extinction, the time to reach $\lfloor \kappa n \rfloor$ satisfies

$$
\mathbb{E}_m\big[T_{\lfloor \kappa n \rfloor} \,\big|\, T_{\lfloor \kappa n \rfloor} < T_0\big] \sim \Big(\frac{1}{\lambda(0)-\mu(0)} - \frac{1}{(\lambda'(\kappa)-\mu'(\kappa))\,\kappa}\Big) \ln n .
$$

3. Conditioned on extinction before reaching carrying capacity, the extinction time converges to that of $m$ independent subcritical lineages, each a linear birth–death process with birth rate $\mu(0)$ and death rate $\lambda(0)$:

$$
\mathbb{E}_m\big[T_0 \,\big|\, T_0 < T_{\lfloor \kappa n \rfloor}\big] \to \int_0^\infty \big(1 - q_t^m\big)\,dt, \qquad q_t = \frac{\lambda(0)\big(1 - e^{-(\lambda(0)-\mu(0))t}\big)}{\lambda(0) - \mu(0)\,e^{-(\lambda(0)-\mu(0))t}} ,
$$

where $q_t$ is the probability that one such lineage has died out by time $t$. For $m = 1$ the limit is $-\frac{1}{\mu(0)} \ln(1 - \rho)$; it increases strictly with $m$ (for $\lambda(0) = 2$, $\mu(0) = 1$ it is $\ln 2 \approx 0.693$ for $m = 1$ and $3\ln 2 - 1 \approx 1.079$ for $m = 2$). The source's Proposition 13 prints the $m = 1$ value for every $m$.

## Depends on

- [Invasion probability and potential barrier of the stochastic logistic process](invasion-probability-and-potential-barrier-of-the-stochastic-logistic-process.md)

## Expansion

The mean extinction time of a birth–death chain is an explicit double sum of products of the ratios $\mu_j/\lambda_j$; writing these products as $e^{nV(i/n)}$ and applying Laplace's method around the minimum of $V$ at $\kappa$ gives the Gaussian prefactor $\sqrt{2\pi/(nV''(\kappa))}$ with $V''(\kappa) = \frac{\mu'(\kappa)}{\mu(\kappa)} - \frac{\lambda'(\kappa)}{\lambda(\kappa)}$. The establishment time is the sum of a supercritical branching phase of length $\ln n/(\lambda(0)-\mu(0))$ and a relaxation phase governed by the linearized rate $-(\lambda'(\kappa)-\mu'(\kappa))\kappa$ at carrying capacity. Conditioning a supercritical branching process on extinction swaps its birth and death rates, and the extinction time of $m$ independent lineages is the maximum of their extinction times, whose law is $q_t^m$; this gives item 3.

## Sources

- Todd L. Parsons, *Invasion probabilities, hitting times, and some fluctuation theory for the stochastic logistic process*, arXiv:1704.02168, Propositions 8, 9 and 13 (Section 3). <https://doi.org/10.48550/arXiv.1704.02168> Published version: Journal of Mathematical Biology 77 (2018) 1193–1231, <https://doi.org/10.1007/s00285-018-1250-x>.
