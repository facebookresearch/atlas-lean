# Traveling-wave self-consistency for fixation probabilities

Consider an asexual (non-recombining) population of size $N$ in which each individual acquires new mutations at total rate $U$ per generation, with fitness effects drawn from a distribution $\rho(s)$, and set $\mu(s) = U\rho(s)$. In the traveling-wave description (Melissa, Good, Fisher and Desai 2022), the population is summarized by the typical distribution $f(x)$ of relative log-fitness $x$ (measured from the population mean) and the probability $w(x)$ that an individual of relative fitness $x$ eventually takes over the population. Under the quasi-deterministic approximation, for $x$ below a cutoff $x_c$ (the "nose"), with $f(x) = 0$ and $w(x) \approx x$ above it:

$$-v\,\partial_x f(x) = x f(x) + \int \mu(s)\bigl[f(x - s) - f(x)\bigr]\,ds, \qquad \int f(x)\,dx = 1,$$

$$v\,\partial_x w(x) \approx x\, w(x) + \int \mu(s)\bigl[w(x + s) - w(x)\bigr]\,ds - w(x)^2,$$

where $v$ is the rate of change of mean fitness. The fixation probability of a new mutation of effect $s$ and the speed are

$$p_{\mathrm{fix}}(s) = \int f(x)\, w(x+s)\,dx, \qquad v = N \int \mu(s)\, s\, p_{\mathrm{fix}}(s)\,ds,$$

and $v$ is fixed self-consistently by the neutral condition

$$p_{\mathrm{fix}}(0) = \int f(x)\, w(x)\,dx \approx \frac1N.$$

The product $N f(x) w(x)$ is the fitness distribution of future common ancestors. The coalescent timescale $T_c$ is defined by $v = \int \mu(s)\, s\, e^{T_c s}\,ds$, and the classical single-site regimes are recovered as limits: the infinitesimal regime when $T_c |s| \ll 1$ for the relevant effects, and the strong-selection regimes when $T_c |s| \gg 1$.

## Depends on

- [Clonal interference](clonal-interference.md)

## Expansion

The deterministic part of the stochastic equation for $f(X,t)$ is selection $(X - \bar X)f$ plus mutation; in the co-moving frame $x = X - \bar X$ a steady profile satisfies the first equation. Each lineage founds an independent branching process that interacts with the others only through $v$; its extinction generating functional satisfies $-\partial_t\phi = x\phi - \phi^2 + \int\mu(s)[\phi(x+s) - \phi(x)]\,ds$, whose co-moving steady state gives the equation for $w$. At large $x$ the terms $xw$ and $w^2$ balance, giving $w \approx x$; at small $x$ the quadratic term is negligible and the equation is linear. Enforcing $\int f w = 1/N$ closes the system. These equations are approximations valid for large $N$; they are not exact statements about a finite Wright–Fisher model.

## Sources

- M. J. Melissa, B. H. Good, D. S. Fisher and M. M. Desai, "Population genetics of polymorphism and divergence in rapidly evolving populations", Genetics 221(4) (2022), iyac053, <https://doi.org/10.1093/genetics/iyac053>, PMCID PMC9339298 (equations (4)–(11) and (17)).
