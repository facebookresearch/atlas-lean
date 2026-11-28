# Binding-site partnership network and its stationary degree distribution

Every individual has **partnership capacity** $n \ge 1$, pictured as $n$ binding sites that are free or occupied. Individuals enter the population at a constant rate and die at per-capita rate $\mu > 0$, so ages are exponentially distributed with density $\mu e^{-\mu a}$. Binding sites behave independently: an occupied site becomes free at rate $\sigma + \mu$ (separation or death of the partner), and a free site becomes occupied at rate $\rho F$, where $\rho > 0$ and $F(t)$ is the fraction of free binding sites in the population. Thus an individual with $k$ partners moves $k \to k+1$ at rate $\rho(n-k)F$ and $k \to k-1$ at rate $(\sigma+\mu)k$; newborns have $k = 0$.

**Proposition.** The fraction of free binding sites satisfies the closed equation

$$\frac{dF}{dt} = \mu + (\sigma + \mu)(1 - F) - \rho F^2 - \mu F,$$

and $F(t) \to \bar F$ as $t \to \infty$, where

$$\bar F = \frac{\sqrt{(\sigma + 2\mu)(4\rho + \sigma + 2\mu)} - (\sigma + 2\mu)}{2\rho},$$

independent of $n$. With $F \equiv \bar F$, a binding site of an individual of age $a$ is occupied with probability

$$\epsilon(a) = \frac{\rho \bar F}{\rho\bar F + \sigma + \mu}\Big(1 - e^{-(\rho \bar F + \sigma + \mu)a}\Big),$$

and the stationary fraction of individuals with $k$ partners is

$$P_k = \binom{n}{k}\int_0^\infty \mu e^{-\mu a}\, \epsilon(a)^k (1 - \epsilon(a))^{n-k}\, da .$$

A newly acquired partner has $k$ partners (counting the new one) with probability $q_k = (n-k+1)P_{k-1}/(n\bar F)$, and one end of a uniformly chosen partnership has $k$ partners with probability $Q_k = k P_k / (n(1-\bar F))$.

## Expansion

Since sites are independent and the age distribution is stationary, the free-site fraction gains $\mu$ from newborns (all sites free), gains $(\sigma+\mu)(1-F)$ from dissolutions, loses $\rho F \cdot F$ from pairing (a free site pairs at rate $\rho F$) and $\mu F$ from deaths, giving a scalar Riccati equation; its unique root in $(0,1)$ solves $\rho F^2 + (\sigma + 2\mu)F - (\sigma + 2\mu) = 0$ and is globally attracting on $[0,1]$. For fixed $F = \bar F$, each site of a living individual is a two-state Markov chain started free, with occupancy probability $\epsilon(a)$; independence of the $n$ sites gives a binomial count, and averaging over the exponential age distribution gives $P_k$. The size-biased laws $q_k$ and $Q_k$ follow because a potential partner with $k-1$ partners offers $n - k + 1$ free sites, and an individual with $k$ partners appears in $k$ partnerships.

## Sources

- K. Y. Leung, M. Kretzschmar, O. Diekmann, "SI infection on a dynamic partnership network: characterization of $R_0$", Journal of Mathematical Biology 71(1) (2015) 1–56, Section 2, Lemma 1, Eqs. (4)–(8) and Lemma 2, <https://doi.org/10.1007/s00285-014-0808-5>, PMCID PMC4430681.
