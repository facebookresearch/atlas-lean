# Limit laws of $\theta$-linear-fractional Galton–Watson processes

**Model.** A Bienaymé–Galton–Watson process $(N_n)_{n \ge 0}$ has offspring probability generating function (pgf) $\phi$ of *$\theta$-linear-fractional* type if, for parameters $|\theta| \le 1$, $a, b > 0$ and $z_c \ge 1$,

$$
\big(z_c - \phi(z)\big)^{-\theta} = a\,(z_c - z)^{-\theta} + b,
$$

for those parameters for which $\phi$ is a pgf with $\phi(1) \le 1$ ($\theta = 0$ is a logarithmic limit; $\theta = 1$ is the classical linear-fractional, i.e. homographic, case, and $\theta = -1$ the Greenwood model). In the variable $w = (z_c - z)^{-\theta}$ the map $\phi$ is affine, so the $n$-th iterate is explicit:

$$
\big(z_c - \phi^{\circ n}(z)\big)^{-\theta} = a^n (z_c - z)^{-\theta} + b\,\frac{a^n - 1}{a - 1} \quad (a \ne 1), \qquad = (z_c - z)^{-\theta} + nb \quad (a = 1).
$$

Take $z_c = 1$ and $\theta \in (0, 1]$; then the mean offspring number is $\mu = a^{-1/\theta}$.

**Theorem.**

1. *(Subcritical, $a > 1$: Yaglom limit.)* $N_n \mid N_n > 0$ converges in law to $N_\infty$ with pgf

$$
\phi_\infty(z) = 1 - \frac{1 - z}{\big(\alpha + \beta (1 - z)^\theta\big)^{1/\theta}}, \qquad \alpha = \frac{a-1}{a+b-1},\ \beta = \frac{b}{a+b-1},
$$

   which solves the Schröder equation $1 - \phi_\infty(\phi(z)) = \mu\,(1 - \phi_\infty(z))$ and has mean $\alpha^{-1/\theta}$. For $\theta \in (0,1)$ its tail is a power law, $\mathbb{P}(N_\infty > k) \sim -\frac{\beta}{\Gamma(-\theta)\,\theta\, \alpha^{1 + 1/\theta}}\, k^{-(1+\theta)}$, so $N_\infty$ has moments only of order $< 1 + \theta$.
2. *(Critical, $a = 1$.)* Extinction is certain but slow: the extinction time $\tau_{i,0}$ from $i$ individuals satisfies $\mathbb{P}(\tau_{1,0} > n) = (1 + nb)^{-1/\theta}$ and $\mathbb{P}(\tau_{i,0} > n) \sim i\,(nb)^{-1/\theta}$, a heavy, non-geometric tail.
3. *(Supercritical with finite mean, $a \in (0,1)$.)* $\mu^{-n} N_n \to W$ in law, where with $\alpha = \frac{1-a}{a+b-1}$, $\beta = \frac{b}{a+b-1}$ the Laplace–Stieltjes transform of $W$ is

$$
\mathbb{E}\, e^{-\lambda W} = 1 - \lambda\, \alpha^{1/\theta} \big(\beta \lambda^\theta + 1\big)^{-1/\theta},
$$

   solving the Poincaré equation $\phi_W(\mu\lambda) = \phi(\phi_W(\lambda))$; the extinction probability is $\rho = 1 - (\alpha/\beta)^{1/\theta}$ and $W$ has an atom of mass $\rho$ at $0$. For $\theta = 1$, $W$ given $W > 0$ is exponential with mean $\beta$.

## Expansion

Conjugating $\phi$ by $z \mapsto (z_c - z)^{-\theta}$ turns iteration into iteration of an affine map, which yields closed forms for $\phi^{\circ n}$ and hence for every limit law: the Yaglom limit is the normalized limit of $1 - \phi^{\circ n}(z)$ divided by $1 - \phi^{\circ n}(0)$, and the supercritical limit is $\lim_n \phi^{\circ n}(e^{-\lambda \mu^{-n}})$. The parameter $\theta$ interpolates between the geometric-type tails of the classical linear-fractional model ($\theta = 1$) and heavy-tailed offspring and limit laws ($\theta < 1$). The source also treats $z_c > 1$ (Yaglom limits with mixed power-law and geometric tails), infinite-mean supercritical cases, Bell-polynomial expressions for the offspring law, and explicit powers of the transition matrix.

## Sources

- N. Grosjean, T. Huillet, "Additional aspects of the generalized linear-fractional branching process", arXiv:1607.01915 (2016): Section 3 (the $\theta$-linear-fractional model and boundary cases), Section 4.1 (Proposition 2 and Corollary 3, subcritical Yaglom limit; Propositions 4–5 for $z_c > 1$; Proposition 6, critical case; Proposition 7 and Corollary 8, supercritical limit $W$). <https://doi.org/10.48550/arXiv.1607.01915> Published version: Annals of the Institute of Statistical Mathematics 69 (2016) 1075–1097, <https://doi.org/10.1007/s10463-016-0573-x>.
