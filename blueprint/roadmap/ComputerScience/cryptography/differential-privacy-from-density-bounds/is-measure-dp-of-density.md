# Density bounds give pure differential privacy for kernels

Let $\mu$ be a σ-finite measure on a measurable space $\Omega$, $\kappa$ a Markov kernel from a measurable space $D$ to $\Omega$, and $\rho : D \to \Omega \to [0, \infty]$ jointly measurable with $\kappa(d) = \rho(d)\cdot\mu$ for every $d$. If $\varepsilon \ge 0$ and, for every ordered pair with $\mathrm{adj}(d, d')$, $\rho(d)(x) \le e^{\varepsilon} \rho(d')(x)$ for $\mu$-almost every $x$, then $\kappa$ is [$(\varepsilon, 0)$-differentially private](../measure-differential-privacy/is-measure-dp.md) for $\mathrm{adj}$.
