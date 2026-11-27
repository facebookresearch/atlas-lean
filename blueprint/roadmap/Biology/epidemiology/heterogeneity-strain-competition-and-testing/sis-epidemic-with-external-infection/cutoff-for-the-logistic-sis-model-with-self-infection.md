# Cutoff for the logistic SIS epidemic with self-infection

**Model.** In a population of size $N$, let $X_N(t) \in \{0,\ldots,N\}$ be the number of infected individuals in the continuous-time Markov chain with transitions

$$x \to x+1 \text{ at rate } \lambda\,\frac{x(N-x)}{N} + \varepsilon (N-x), \qquad x \to x-1 \text{ at rate } \mu x,$$

with fixed constants $\lambda, \mu, \varepsilon > 0$ (contact infection, external infection, recovery). Its fluid limit is $\dot x = \lambda x(1-x) + \varepsilon(1-x) - \mu x$, whose unique equilibrium $x^\star \in (0,1)$ is globally attracting on $[0,1]$, with

$$x(t) = x^\star + \frac{\frac{J}{\lambda}(\alpha - x^\star)}{(\alpha - x_1^\star)e^{tJ} - (\alpha - x^\star)}, \qquad J = \sqrt{(\lambda-\mu-\varepsilon)^2 + 4\lambda\varepsilon},$$

for $x(0) = \alpha$, where $x_1^\star < 0$ is the other root of the right-hand side. Because $\varepsilon > 0$, the chain is irreducible with stationary law $\pi_N$.

**Cutoff.** A sequence of chains has *cutoff* at $t_N$ with window $\omega_N = o(t_N)$ if the worst-case total variation distance $\rho_N(t) = \max_x \|P^t_N(x,\cdot) - \pi_N\|_{\mathrm{TV}}$ satisfies $\lim_{s\to\infty}\liminf_N \rho_N(t_N - s\omega_N) = 1$ and $\lim_{s\to\infty}\limsup_N \rho_N(t_N + s\omega_N) = 0$.

**Theorem.** The chains $(X_N)_{N \ge 1}$ exhibit cutoff at

$$t_N = \frac{1}{2J}\log N$$

with a window of constant size.

## Depends on

- [Extinction time of the stochastic logistic SIS epidemic](../../sis-epidemic-model/extinction-time-of-the-stochastic-logistic-epidemic.md)

## Expansion

Near $x^\star$ the fluid limit contracts at exponential rate $|f'(x^\star)| = J$, while stationary fluctuations of $X_N/N$ are of order $N^{-1/2}$. A chain started at distance of order $1$ from $x^\star$ therefore needs time $\frac{1}{J}\log\sqrt N = \frac{1}{2J}\log N$ for its deterministic error to shrink to the size of the noise, which gives the lower bound. For the upper bound, two copies are coupled: both follow the ODE into an $N^{-1/2}$-neighbourhood of $x^\star$ by time $(1-h)\frac{1}{2J}\log N$, and from there their difference behaves like a contracting random walk with jump rates of order $N$, which coalesces in constant time. Unlike the classical SIS model ($\varepsilon=0$), all transition rates stay of order $N$ near equilibrium, which is what makes the window constant.

## Sources

- Roxanne He, Malwina Luczak and Nathan Ross, "Cutoff for the logistic SIS epidemic model with self-infection", Advances in Applied Probability 57 (2025), 1456–1483, <https://doi.org/10.1017/apr.2025.16>; numbering as in arXiv:2407.18446: Definition 1.1, Theorem 1.2 and Proposition 2.1.
