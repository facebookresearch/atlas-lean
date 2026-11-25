# Density bounds give event bounds

Let $D$ and $\Omega$ be measurable spaces, $\mu$ a σ-finite measure on $\Omega$, and $\kappa$ a Markov kernel from $D$ to $\Omega$. Let $\rho : D \to \Omega \to [0, \infty]$ be jointly measurable with $\kappa(d) = \rho(d)\cdot\mu$ (the measure with density $\rho(d)$ against $\mu$) for every $d$. Let $\mathrm{adj}$ be a relation on $D$ and $\varepsilon \ge 0$, and suppose that for every ordered pair with $\mathrm{adj}(d, d')$,

$$
\rho(d)(x) \le e^{\varepsilon}\, \rho(d')(x) \quad \text{for } \mu\text{-almost every } x .
$$

Then for every such pair and every measurable $S \subseteq \Omega$, $\kappa(d)(S) \le e^{\varepsilon}\, \kappa(d')(S)$.
