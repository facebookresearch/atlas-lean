# Kernel differential privacy with zero delta

A Markov kernel $\kappa$ from $D$ to $\Omega$ is [$(\varepsilon, 0)$-differentially private](is-measure-dp.md) for $\mathrm{adj}$ if and only if $\varepsilon \ge 0$ and, for every ordered pair with $\mathrm{adj}(d, d')$ and every measurable $S \subseteq \Omega$,

$$
\kappa(d)(S) \le e^{\varepsilon}\, \kappa(d')(S).
$$
