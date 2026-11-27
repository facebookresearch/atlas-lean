# Exponential dose–response from independent exposures

**Setting.** Let $P(n) \in [0,1]$ be the probability that a host escapes infection after exposure to $n \ge 0$ infectious particles (virions), with $n$ treated as a nonnegative real dose. Assume

1. $P$ is nonincreasing, $P(0) = 1$, and $P(n) > 0$ for some $n > 0$ (the source assumes $P$ strictly decreasing, which, with the functional equation below, also forces this);
2. *no immunological memory of unsuccessful challenges*: escaping a dose $n_1$ does not change the response to a subsequent dose $n_2$, so

$$P(n_1 + n_2) = P(n_1)\, P(n_2) \qquad \text{for all } n_1, n_2 \ge 0 .$$

**Proposition.** Under these assumptions there is a constant $\alpha \ge 0$ (units: per virion) with

$$P(n) = e^{-\alpha n}, \qquad n \ge 0,$$

so the infection probability is $1 - e^{-\alpha n}$. If $\mathrm{ID}_{50}$ denotes the dose at which half of exposed hosts are infected, then $\alpha = \ln 2 / \mathrm{ID}_{50}$ (such a dose exists exactly when $\alpha > 0$).

**Corollary (environmental force of infection).** Suppose a host undergoes exposure events at the times of a Poisson process with rate $\rho$, and each exposure at time $t$ is to the whole environmental virus pool of size $V(t)$, a dose $V(t)$. Then infection from the environment is a Poisson process with rate $\rho\,\big(1 - e^{-\alpha V(t)}\big)$ per susceptible host, and the environmental transmission term for $S$ susceptible hosts is

$$\rho\,\big(1 - e^{-\alpha V(t)}\big)\, S(t).$$

The rate is at most $\rho$, and it reduces to $\alpha\rho V(t)\, S(t)$ to first order when $\alpha V(t) \ll 1$.

## Expansion

The functional equation is the exponential Cauchy equation. The positivity hypothesis is needed: $P(0) = 1$ and $P(n) = 0$ for $n > 0$ satisfies monotonicity and the functional equation but is not exponential. Given $P(n_0) > 0$ with $n_0 > 0$, monotonicity gives $P > 0$ on $[0, n_0]$ and multiplicativity gives $P(m n_0) = P(n_0)^m > 0$ for every integer $m \ge 1$, so $P > 0$ on $[0, \infty)$. Hence $g = -\ln P$ is additive and monotone on $[0,\infty)$, and monotone solutions of Cauchy's additive equation are linear, $g(n) = \alpha n$. Setting $1 - e^{-\alpha\,\mathrm{ID}_{50}} = 1/2$ gives $\alpha$. For the corollary, by the proposition an exposure at time $t$ infects with probability $1 - e^{-\alpha V(t)}$, and by the no-memory assumption exposures that the host escapes do not change later responses, so infecting exposures are an independent thinning of the exposure process: a Poisson process with intensity $\rho(1 - e^{-\alpha V(t)})$. Since $1 - e^{-x} \le x$ with equality to first order at $x = 0$, the linear term $\alpha\rho V$ is an upper bound and the small-dose approximation.

## Sources

- Breban R, Drake JM, Stallknecht DE, Rohani P, "The role of environmental transmission in recurrent avian influenza epidemics" (2009), section "Model" (exponential Cauchy equation for the escape probability, $\mathrm{ID}_{50}$ relation, and the environmental transmission rate $\rho(1 - e^{-\alpha V})$ per susceptible), <https://doi.org/10.1371/journal.pcbi.1000346>, PMCID PMC2660440.
