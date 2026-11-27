# Negative binomial and Gamma laws of a CMJ population with immigration

**Splitting trees.** In a homogeneous binary Crump–Mode–Jagers (CMJ) process, individuals have i.i.d. lifetimes with law $\Lambda(\cdot)/b$, where $\Lambda$ is a positive measure on $(0,\infty)$ of mass $b$, and give birth to single children at constant rate $b$ during life. Assume supercriticality, $m = \int r\,\Lambda(dr) > 1$. Let

$$\psi(\lambda) = \lambda - \int_{(0,\infty)}(1 - e^{-\lambda r})\,\Lambda(dr), \qquad \lambda \ge 0;$$

$\psi$ is convex with a unique positive root $\eta$, the Malthusian parameter, and $c := \psi'(\eta) > 0$. The **scale function** $W$ is the increasing function with $\int_0^\infty e^{-\lambda x}W(x)\,dx = 1/\psi(\lambda)$ for $\lambda > \eta$. A single CMJ population $X$ started from one newborn goes extinct with probability $1 - \eta/b$, and on survival $e^{-\eta t}X(t) \to E$ a.s. with $E \sim \mathrm{Exp}(c)$.

**Immigration.** Immigrants arrive at the times $T^{(1)} < T^{(2)} < \cdots$ of a Poisson process of rate $\theta$, each founding an independent copy of the CMJ population. Let $I(t)$ be the total number of individuals alive at time $t$.

**Theorem.**

1. For each $t > 0$, $I(t)$ is negative binomial with parameters $1 - W(t)^{-1}$ and $\theta/b$:

$$\mathbb E\big[s^{I(t)}\big] = \left(\frac{W(t)^{-1}}{1 - s\,(1 - W(t)^{-1})}\right)^{\theta/b}, \qquad s \in [0,1].$$

2. Almost surely,

$$\lim_{t\to\infty} e^{-\eta t}I(t) = \sum_{i\ge1} e^{-\eta T^{(i)}}E_i =: I,$$

with $E_i$ i.i.d. copies of $E$ independent of the arrival times, and $I \sim \Gamma(\theta/b, c)$, with density $c^{\theta/b}x^{\theta/b-1}e^{-cx}/\Gamma(\theta/b)$ on $(0,\infty)$.

The almost-sure convergence for a single population holds without a finite-variance assumption on offspring numbers; it only uses a log-integrability bound on $\sup_t e^{-\eta t}X(t)$ obtained by spine decomposition of the splitting tree.

## Expansion

The contour of a splitting tree is a spectrally positive Lévy process with Laplace exponent $\psi$, so two-sided exit probabilities are ratios of scale functions: started from an ancestor with residual lifetime $x$, $\mathbb P_x(X(t) = 0) = W(t-x)/W(t)$, and given $X(t) \ne 0$ the population size is geometric with success probability $1/W(t)$. Superposing Poisson-many founders and integrating over their arrival times turns these geometric laws into a negative binomial with shape $\theta/b$. Since $e^{-\eta t}W(t) \to 1/c$, the rescaled sum converges to a Poisson functional of exponential variables, whose Laplace transform is that of a $\Gamma(\theta/b,c)$ law; the series converges because $\mathbb E[\log^+ E] < \infty$.

## Sources

- Mathieu Richard, "Limit theorems for supercritical age-dependent branching processes with neutral immigration", arXiv (2010). Section 2 (splitting trees, Proposition 2.1, Theorem 2.3), Sections 3–4 (spine decomposition, Lemmas 3.1–4.2). <https://doi.org/10.48550/arXiv.1007.5428>. Published version: Advances in Applied Probability 43(1) (2011), 276–300, <https://doi.org/10.1239/aap/1300198523>; locators above refer to the arXiv version.
