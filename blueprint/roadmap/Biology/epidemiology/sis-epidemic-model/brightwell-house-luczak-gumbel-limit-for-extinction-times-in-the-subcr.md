# Gumbel limit for extinction times in the subcritical SIS logistic epidemic

In the stochastic SIS logistic epidemic on a population of $N$ individuals, each infective infects each susceptible at rate $\lambda/N$ and recovers at rate $\mu$; let $X_N(t)$ be the number of infectives and $T_N$ the extinction time. Brightwell, House and Luczak (2018, Theorem 1.1) prove: if $\mu = \mu(N)$ and $\lambda = \lambda(N)$ are bounded away from $0$ and $\infty$, $(\mu - \lambda)N^{1/2} \to \infty$, $X_N(0)$ is non-random and $X_N(0)(\mu - \lambda) \to \infty$, then
$$(\mu - \lambda)T_N - \log N + 2\log(\mu - \lambda) - \log\Bigl(1 + \frac{(\mu - \lambda)N}{\lambda X_N(0)}\Bigr) - \log\mu - \log\lambda \;\to\; W$$
in distribution, where $W$ has the standard Gumbel law $P(W \le w) = e^{-e^{-w}}$ (Eq. (1.4)). This covers both fixed $\lambda < \mu$ and the near-critical regime in which $\mu - \lambda \to 0$ more slowly than $N^{-1/2}$.

## Expansion

1. The model: the birth–death chain on $\{0, \dots, N\}$ with rates $\lambda x(N - x)/N$ and $\mu x$, its absorbing state and extinction time.
2. The hypotheses: bounded rates, the scaling $(\mu - \lambda)N^{1/2} \to \infty$ and the initial condition.
3. The coupling and martingale estimates of the source for the approach to a small number of infectives, and the final Gumbel limit.
4. The special cases $X_N(0)/N \to \alpha$ (Eq. (1.5)) and $X_N(0)/(N(\mu - \lambda)) \to \infty$ (Eq. (1.6)); the source also notes that an earlier published formula for this limit was erroneous.

## Sources

- G. Brightwell, T. House and M. Luczak, Extinction times in the subcritical stochastic SIS logistic epidemic, J. Math. Biol. 77 (2018), 455–493, Theorem 1.1 and Eqs. (1.4)–(1.6). <https://arxiv.org/abs/1312.7449>
