# Approximate differential privacy for Markov kernels

Let $\kappa$ be a Markov kernel from a measurable space $D$ of databases to a measurable space $\Omega$ of outputs, $\mathrm{adj}$ a relation on $D$ and $\varepsilon, \delta \in \mathbb{R}$. The kernel is $(\varepsilon, \delta)$-differentially private when $\varepsilon \ge 0$, $\delta \ge 0$ and the family of measures $\kappa(d)$ is [$(\varepsilon, \delta)$-differentially private](../differential-privacy/differentially-private.md): for every ordered pair with $\mathrm{adj}(d, d')$ and every measurable $S \subseteq \Omega$,

$$
\kappa(d)(S) \le e^{\varepsilon}\, \kappa(d')(S) + \delta .
$$
