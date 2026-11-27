# Invasion probability and potential barrier of the stochastic logistic process

Let $\lambda, \mu : [0,\infty) \to [0,\infty)$ be continuous per-capita birth and death rates, $\lambda$ non-increasing and $\mu$ non-decreasing with $x \mapsto \ln(\mu(x)/\lambda(x))$ increasing, and suppose there is a carrying capacity $\kappa > 0$ with $\lambda(x) > \mu(x)$ on $(0,\kappa)$, $\lambda(\kappa) = \mu(\kappa)$ and $\lambda(x) < \mu(x)$ for $x > \kappa$; in particular $\lambda(0) > \mu(0)$. For a scale parameter $n$, let $X^{(n)}$ be the birth–death chain on $\{0,1,2,\dots\}$ with rates

$$
i \to i+1 \ \text{ at rate } \ i\,\lambda(i/n), \qquad i \to i-1 \ \text{ at rate } \ i\,\mu(i/n),
$$

and let $T_m$ be its hitting time of $m$. Define the potential $V(\iota) = \int_0^\iota \ln\frac{\mu(x)}{\lambda(x)}\,dx$, which decreases on $[0,\kappa]$ and increases afterwards, and let $\eta > \kappa$ be the potential barrier, the point with $V(\eta) = V(0) = 0$.

**Theorem.**

1. For every $0 < \iota < \eta$ and every fixed initial size $m \ge 1$,

$$
\lim_{n\to\infty} \mathbb{P}_m\{T_0 < T_{\lfloor \iota n \rfloor}\} = \Big(\frac{\mu(0)}{\lambda(0)}\Big)^m ,
$$

so the population reaches density $\iota$, even far above carrying capacity, with limiting probability $1 - (\mu(0)/\lambda(0))^m$, the survival probability of the linear branching process with rates $\lambda(0), \mu(0)$.
2. If $m_n \to \infty$, then $\mathbb{P}_{m_n}\{T_0 < T_{\lfloor \iota n \rfloor}\} \to 0$ for every $\iota < \eta$: an established population exceeds every density below $\eta$ before extinction with high probability.
3. If $\iota > \eta$ and $m_n < \nu n$ for some $\nu < \iota$, then $\mathbb{P}_{m_n}\{T_0 < T_{\lfloor \iota n \rfloor}\} \to 1$: the rescaled process $X^{(n)}/n$ is asymptotically stochastically bounded by $\eta + \varepsilon$ for every $\varepsilon > 0$.

## Expansion

The gambler's-ruin formula for birth–death chains gives

$$
\mathbb{P}_m\{T_a < T_b\} = \frac{\sum_{i=m}^{b-1} \prod_{j=1}^{i} \mu_j/\lambda_j}{\sum_{i=a}^{b-1} \prod_{j=1}^{i} \mu_j/\lambda_j},
$$

and $\prod_{j \le \iota n} \mu_j/\lambda_j = e^{n V(\iota) + o(n)}$. The sums are dominated by the endpoints of lowest potential (a Laplace-type argument), so the process can reach exactly the densities whose potential lies below the starting potential $V(0) = 0$. Near $\kappa$ the potential is locally symmetric, which is why an established population overshoots the carrying capacity by an amount of order $n$ (up to the barrier $\eta$) before going extinct.

## Sources

- Todd L. Parsons, *Invasion probabilities, hitting times, and some fluctuation theory for the stochastic logistic process*, arXiv:1704.02168, Propositions 1, 2 and 3 (Section 2). <https://doi.org/10.48550/arXiv.1704.02168> Published version: Journal of Mathematical Biology 77 (2018) 1193–1231, <https://doi.org/10.1007/s00285-018-1250-x>.
