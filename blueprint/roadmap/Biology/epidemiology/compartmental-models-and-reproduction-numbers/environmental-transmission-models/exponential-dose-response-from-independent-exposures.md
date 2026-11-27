# Exponential dose–response from independent exposures

**Setting.** Let $P(n) \in [0,1]$ be the probability that a host escapes infection after exposure to $n \ge 0$ infectious particles (virions), with $n$ treated as a nonnegative real dose. Assume

1. $P$ is nonincreasing, $P(0) = 1$, and $P(n) > 0$ for some $n > 0$ (the source assumes $P$ strictly decreasing, which, with the functional equation below, also forces this);
2. *no immunological memory of unsuccessful challenges*: escaping a dose $n_1$ does not change the response to a subsequent dose $n_2$, so

$$P(n_1 + n_2) = P(n_1)\, P(n_2) \qquad \text{for all } n_1, n_2 \ge 0 .$$

**Proposition.** Under these assumptions there is a constant $\alpha \ge 0$ (units: per virion) with

$$P(n) = e^{-\alpha n}, \qquad n \ge 0,$$

so the infection probability is $1 - e^{-\alpha n}$. If $\mathrm{ID}_{50}$ denotes the dose at which half of exposed hosts are infected, then $\alpha = \ln 2 / \mathrm{ID}_{50}$ (such a dose exists exactly when $\alpha > 0$).

**Corollary (environmental force of infection).** If a host ingests a fraction $\rho$ per unit time of an environmental virus pool of size $V(t)$ (so it receives dose $\rho V(t)\,dt$ in $[t, t + dt]$), then infection from the environment is a Poisson process with rate $\alpha \rho V(t)$, and the environmental transmission term for $S$ susceptible hosts is $\alpha\rho V(t)\, S(t)$.

## Expansion

The functional equation is the exponential Cauchy equation. The positivity hypothesis is needed: $P(0) = 1$ and $P(n) = 0$ for $n > 0$ satisfies monotonicity and the functional equation but is not exponential. Given $P(n_0) > 0$ with $n_0 > 0$, monotonicity gives $P > 0$ on $[0, n_0]$ and multiplicativity gives $P(m n_0) = P(n_0)^m > 0$ for every integer $m \ge 1$, so $P > 0$ on $[0, \infty)$. Hence $g = -\ln P$ is additive and monotone on $[0,\infty)$, and monotone solutions of Cauchy's additive equation are linear, $g(n) = \alpha n$. Setting $1 - e^{-\alpha\,\mathrm{ID}_{50}} = 1/2$ gives $\alpha$. For the corollary, the escape probability over $[0,t]$ is $\exp(-\alpha\rho\int_0^t V(s)\,ds)$ by multiplicativity over small time steps, which is the survival function of an inhomogeneous Poisson process with intensity $\alpha\rho V$. Only the product $\alpha\rho$, the per-virion infectiousness times the exposure rate, enters the dynamics, so these two parameters are not separately identifiable from incidence data.

## Sources

- Breban R, Drake JM, Stallknecht DE, Rohani P, "The role of environmental transmission in recurrent avian influenza epidemics" (2009), section "Model" (exponential Cauchy equation for the escape probability, $\mathrm{ID}_{50}$ relation and exposure rate), <https://doi.org/10.1371/journal.pcbi.1000346>, PMCID PMC2660440.
