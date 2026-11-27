# Sharp extinction and establishment times of the stochastic logistic process

Let $X^{(n)}$ be the [stochastic logistic process](invasion-probability-and-potential-barrier-of-the-stochastic-logistic-process.md) with per-capita rates $\lambda(i/n)$, $\mu(i/n)$, carrying capacity $\kappa$ and potential $V(\iota) = \int_0^\iota \ln(\mu(x)/\lambda(x))\,dx$, and assume moreover that $\lambda$ and $\mu$ are differentiable at $\kappa$ with $\frac{\mu'(\kappa)}{\mu(\kappa)} - \frac{\lambda'(\kappa)}{\lambda(\kappa)} > 0$. Write $\rho = \mu(0)/\lambda(0) < 1$ and fix an initial size $m \ge 1$.

**Theorem.** As $n \to \infty$:

1. The expected extinction time is exponentially large in $n$, with rate the depth $-V(\kappa) > 0$ of the potential well at carrying capacity: for every fixed $m$,

$$
\lim_{n\to\infty}\frac1n\ln\mathbb{E}_m[T_0] = -V(\kappa).
$$

   The source's Proposition 8 prints a sharp asymptotic in which the whole right-hand side, including $e^{-nV(\kappa)}$ and a factor $1-\lambda(0)/\mu(0)<0$, stands under one square root, so it gives no positive constant and, read literally, the wrong rate. This page states only the exponential rate, which follows by direct computation from the last display of the source's proof, $\mathbb{E}_m[T_0]\sim\frac{1-\rho^m}{1-\rho}\sum_{i=1}^{\lfloor\eta n\rfloor}e^{-nV((i-1)/n)}\big/\big(n\mu(\tfrac in)\tfrac in\sqrt{\mu(\tfrac{i-1}n)\lambda(0)/(\lambda(\tfrac{i-1}n)\mu(0))}\big)$: each of the at most $\eta n$ terms is at most $e^{-nV(\kappa)}$ times a factor polynomial in $n$, and the terms with $i/n$ near $\kappa$ are of that size, because $-V$ is maximized at $\kappa$.
2. Conditioned on reaching carrying capacity before extinction, the time to reach $\lfloor \kappa n \rfloor$ satisfies

$$
\mathbb{E}_m\big[T_{\lfloor \kappa n \rfloor} \,\big|\, T_{\lfloor \kappa n \rfloor} < T_0\big] \sim \Big(\frac{1}{\lambda(0)-\mu(0)} - \frac{1}{(\lambda'(\kappa)-\mu'(\kappa))\,\kappa}\Big) \ln n .
$$

3. Started from a single individual ($m=1$) and conditioned on extinction before reaching carrying capacity, the extinction time converges in mean to that of a subcritical linear birth–death process with birth rate $\mu(0)$ and death rate $\lambda(0)$:

$$
\lim_{n\to\infty}\mathbb{E}_1\big[T_0 \,\big|\, T_0 < T_{\lfloor \kappa n \rfloor}\big] = -\frac{1}{\mu(0)} \ln(1 - \rho).
$$

   The source's Proposition 13 prints this same limit for every fixed $m<\lfloor\kappa n\rfloor$; this page states it only for $m=1$, because for $m\ge2$ the conditioned process starts from $m$ lineages and its limit should be $\int_0^\infty(1-q_t^m)\,dt$ (with $q_t$ the extinction probability by time $t$ of one subcritical lineage), which differs from the $m=1$ value, and the source displays no argument for that case.

## Depends on

- [Invasion probability and potential barrier of the stochastic logistic process](invasion-probability-and-potential-barrier-of-the-stochastic-logistic-process.md)

## Expansion

The mean extinction time of a birth–death chain is an explicit double sum of products of the ratios $\mu_j/\lambda_j$; writing these products as $e^{nV(i/n)}$ and applying Laplace's method around the minimum of $V$ at $\kappa$ shows that the sum is $e^{-nV(\kappa)+o(n)}$ (with a Gaussian prefactor of order $\sqrt{2\pi/(nV''(\kappa))}$, $V''(\kappa) = \frac{\mu'(\kappa)}{\mu(\kappa)} - \frac{\lambda'(\kappa)}{\lambda(\kappa)}$, which does not affect the rate). The establishment time is the sum of a supercritical branching phase of length $\ln n/(\lambda(0)-\mu(0))$ and a relaxation phase governed by the linearized rate $-(\lambda'(\kappa)-\mu'(\kappa))\kappa$ at carrying capacity. Conditioning a supercritical branching process on extinction swaps its birth and death rates; for a linear birth–death process with birth rate $\mu(0)$ and death rate $\lambda(0)$ started from one individual, the expected extinction time is $\frac{1}{\mu(0)}\ln\frac{\lambda(0)}{\lambda(0)-\mu(0)}=-\frac1{\mu(0)}\ln(1-\rho)$, which gives item 3. For item 1 only the exponential order of the Laplace sum is used.

## Sources

- Todd L. Parsons, *Invasion probabilities, hitting times, and some fluctuation theory for the stochastic logistic process*, arXiv:1704.02168, Propositions 8 (and the last display of its proof), 9 and 13 (Section 3). <https://doi.org/10.48550/arXiv.1704.02168> Published version: Journal of Mathematical Biology 77 (2018) 1193–1231, <https://doi.org/10.1007/s00285-018-1250-x>.
