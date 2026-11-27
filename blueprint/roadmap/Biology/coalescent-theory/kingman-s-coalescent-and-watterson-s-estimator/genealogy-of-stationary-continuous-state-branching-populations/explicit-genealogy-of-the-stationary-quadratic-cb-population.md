# Explicit genealogy of the stationary Feller diffusion with quadratic branching

Take the quadratic sub-critical branching mechanism

$$\psi(\lambda) = \beta\lambda^2 + 2\beta\theta\lambda, \qquad \beta > 0,\ \theta > 0,$$

for which $u(\lambda,t) = \dfrac{2\theta\lambda}{(2\theta+\lambda)e^{2\theta\beta t} - \lambda}$ and $c(t) = \dfrac{2\theta}{e^{2\theta\beta t} - 1}$. Let $Z$ be the stationary CB with immigration (the stationary Feller diffusion with immigration, the Q-process of the sub-critical Feller diffusion conditioned on non-extinction) at time $0$, $A$ its TMRCA, $Z^A$ the population size just before the MRCA, $Z^O$ the size at time $0$ of the oldest clan and $Z^I = Z - Z^O$. Let $\mathbf e_1,\dots,\mathbf e_5$ be i.i.d. exponential random variables with mean $1$.

**Theorem.**

1. $\mathbb E[e^{-\lambda Z}] = \big(\tfrac{2\theta}{2\theta+\lambda}\big)^2$, i.e. $Z \overset{d}{=} (\mathbf e_1 + \mathbf e_2)/(2\theta)$ is Gamma$(2, 2\theta)$.
2. $\mathbb P(A\le t) = (1 - e^{-2\theta\beta t})^2$, i.e. $A \overset{d}{=} \max(\mathbf e_1,\mathbf e_2)/(2\theta\beta)$.
3. Conditionally on $A = t$,

$$\big(Z^A, Z^I, Z^O\big) \overset{d}{=} \Big(\frac{\mathbf e_1+\mathbf e_2}{2\theta + c(t)},\ \frac{\mathbf e_3+\mathbf e_4}{2\theta + c(t)},\ \frac{\mathbf e_5}{2\theta + c(t)}\Big).$$

4. (**Quantified bottleneck.**) Almost surely $\mathbb P(Z^A < Z\mid A) = \tfrac{11}{16}$ and $\mathbb E[Z^A\mid A] = \tfrac23\,\mathbb E[Z\mid A]$; hence $\mathbb P(Z^A < Z) = \tfrac{11}{16}$ and $\mathbb E[Z^A] = \tfrac23\,\mathbb E[Z]$: on average the population just before its MRCA is one third smaller than the current population.
5. Conditionally on $Z$, $\mathbb{P}(A \le t \mid Z) = e^{-c(t)Z} = \mathbb{P}_Z(\zeta \le t)$: given $Z$, $A$ has the law of the extinction time $\zeta$ of a CB started from $Z$.

## Depends on

- [TMRCA and the bottleneck at the MRCA of a stationary CB population](tmrca-and-bottleneck-at-the-mrca-of-a-stationary-cb-population.md)

## Expansion

Substituting the closed forms of $u$ and $c$ into the general joint Laplace transform reduces every factor to a power of a ratio $\tfrac{2\theta + c(t)}{2\theta + c(t) + \lambda}$, which identifies Gamma laws with integer shapes. Given $A$, $Z^A$ is Gamma$(2)$ and $Z = Z^I + Z^O$ is an independent Gamma$(3)$, both at rate $2\theta + c(t)$, so $\mathbb E[Z^A\mid A]/\mathbb E[Z\mid A] = 2/3$, and $\mathbb P(Z^A < Z\mid A)$ is the probability that at least two of the first four points of a merged pair of equal-rate Poisson processes come from the $Z^A$ stream, $\sum_{k=2}^{4}\binom4k 2^{-4} = 11/16$. Because these ratios do not depend on $A$, the conditional statements hold unconditionally.

## Sources

- Yu-Ting Chen, Jean-François Delmas, "Smaller population size at the MRCA time for stationary branching processes", *The Annals of Probability* 40 (2012), 2034–2068, <https://doi.org/10.1214/11-AOP668>; preprint arXiv:1009.0814, <https://doi.org/10.48550/arXiv.1009.0814>. Numbering of the arXiv version: Section 7, Theorem 7.1, Corollary 7.2, Proposition 7.3.
