# Negative binomial law of the birth–death–immigration infected process

**Model.** Let $I(t) \in \{0, 1, 2, \dots\}$ be the number of infected individuals in a large susceptible population, modeled as a linear birth–death process with immigration (BDI): each infected individual infects a new one at rate $\lambda > 0$ and recovers or is removed at rate $\mu \ge 0$, and infections arrive from outside at rate $\nu > 0$. From state $n$ the jumps are $n \to n+1$ at rate $\lambda n + \nu$ and $n \to n-1$ at rate $\mu n$. Set

$$a = \lambda - \mu, \qquad r = \frac{\nu}{\lambda}, \qquad \beta(t) = \frac{\lambda(e^{at} - 1)}{\lambda e^{at} - \mu}.$$

**Theorem.** If $I(0) = 0$, then for every $t > 0$ the probability generating function of $I(t)$ is

$$G(z,t) = \mathbb{E}\big[z^{I(t)}\big] = \Big(\frac{1 - \beta(t)}{1 - \beta(t)\,z}\Big)^r,$$

so $I(t)$ has the (generalized, $r$ need not be an integer) negative binomial distribution

$$P[I(t) = n] = \binom{n + r - 1}{n}\big(1 - \beta(t)\big)^r \beta(t)^n, \qquad n = 0, 1, 2, \dots$$

For $a = 0$ this reads $\beta(t) = \mu t/(1 + \mu t)$. Its mean and variance are $r\beta/(1-\beta)$ and $r\beta/(1-\beta)^2$.

**Proposition (coefficient of variation).** In the supercritical case $\lambda > \mu$, the coefficient of variation $c(t) = \sqrt{\operatorname{Var} I(t)}/\mathbb{E} I(t) = 1/\sqrt{r\beta(t)}$ converges to

$$\lim_{t \to \infty} c(t) = \sqrt{1/r} = \sqrt{\lambda/\nu},$$

and is already close to this limit once $(\lambda - \mu)t \ge 7$. When the immigration rate is small compared with the per-capita infection rate ($r \ll 1$), the epidemic size is therefore highly variable across realizations, no matter how long the epidemic has grown.

## Expansion

The forward equations give the first-order PDE $\partial_t G = (z - 1)(\lambda z - \mu)\partial_z G + \nu(z - 1)G$ with $G(z, 0) = 1$, solved by characteristics. Algebraically $(1 - \beta)/(1 - \beta z) = a/\big(\lambda e^{at} - \mu - \lambda(e^{at} - 1)z\big)$. As $t \to \infty$ with $\lambda > \mu$, $\beta(t) \to 1$ while $\mathbb{E}I(t) \sim r e^{at}\lambda/a$ grows exponentially, so the distribution of $I(t)/\mathbb{E}I(t)$ tends to a Gamma law with shape $r$, whose coefficient of variation is $1/\sqrt r$. For $\mu > \lambda$ the process instead converges to the stationary negative binomial law with parameter $\lambda/\mu$. The negative binomial can also be represented as a compound Poisson distribution, which links the BDI model to clustered (super-spreading) case counts.

## Sources

- H. Kobayashi, "Stochastic Modeling of an Infectious Disease, Part I: Understand the Negative Binomial Distribution and Predict an Epidemic More Reliably", arXiv:2006.01586 (2020), Section 3 (BDI model), Section 4.1 (time-dependent negative binomial solution), Section 5.1 (Proposition 1) and Appendix A (PGF derivation), <https://doi.org/10.48550/arXiv.2006.01586>.
