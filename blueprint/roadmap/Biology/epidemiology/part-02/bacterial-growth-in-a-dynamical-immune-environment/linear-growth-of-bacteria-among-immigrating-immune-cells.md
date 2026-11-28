# Linear growth of bacteria among immigrating immune cells

**Model.** A discrete-time particle system on $\mathbb Z^d$ ($d \ge 1$) with states $0$ (empty), $1$ (bacterium) and $2$ (immune cell), driven by independent Bernoulli variables at each time step. In one step:

- each bacterium colonizes each site $k$ with $\|k - i\|_1 \le 1$ (including its own site) with probability $p$;
- each immune cell colonizes each such neighbouring site with probability $q$;
- an immune cell immigrates at each site independently with probability $\alpha$;
- a site becomes $2$ if it receives an immune cell, otherwise $1$ if it receives a bacterium, otherwise $0$.

So immune cells evolve autonomously, as subcritical oriented percolation reinforced by immigration, and form a dynamical hostile environment in which the bacteria try to grow as an oriented percolation. Let $\vec p_c(d+1)$ be the critical value of independent oriented bond percolation on $\mathbb Z^d \times \mathbb N$ with an oriented edge from $(z,n)$ to $(z',n+1)$ whenever $\|z'-z\|_1 \le 1$. Starting from one bacterium at $0$ and immune cells on $E \subset \mathbb Z^d\setminus\{0\}$, let $\tau_1^{0,E}$ be the bacterial extinction time and $t_1^{0,E}(x)$ the first time site $x$ is occupied by bacteria.

**Theorem.** Let $p > \vec p_c(d+1)$ (bacteria supercritical) and $q < \vec p_c(d+1)$ (immune cells subcritical without immigration).

1. (The phase transition does not depend on the initial environment.) For every $\alpha \in [0,1]$, $\mathbb P_{p,q,\alpha}(\tau_1^{0,\mathbb Z^d\setminus\{0\}} = \infty) > 0$ if and only if $\mathbb P_{p,q,\alpha}(\tau_1^{0,\varnothing} = \infty) > 0$. This defines a critical immigration rate $\alpha_c(p,q)$, and $0 < \alpha_c(p,q) < 1$.
2. (Linear growth.) For every $\alpha < \alpha_c(p,q)$ there are constants $A, B, C > 0$ such that for all $E \subset \mathbb Z^d\setminus\{0\}$, $x \in \mathbb Z^d$ and $t > 0$:

$$\mathbb P\bigl(\tau_1^{0,E} = \infty\bigr) > 0, \qquad \mathbb P\bigl(\tau_1^{0,E} = \infty,\ t_1^{0,E}(x) \ge C\|x\|_1 + t\bigr) \le Ae^{-Bt}, \qquad \mathbb P\bigl(t < \tau_1^{0,E} < \infty\bigr) \le Ae^{-Bt}.$$

So, as long as immune immigration is below the critical rate, an infection that survives spreads at a linear speed, as in the absence of immune cells, and an infection that dies out does so quickly.

## Expansion

The bacteria see the oriented graph with every space-time site removed that is reached by an immune cluster. Since immune clusters are subcritical, they are small and decorrelate exponentially fast, so the bacteria perform a dependent oriented percolation with unbounded but exponentially decaying dependence. A Liggett–Schonmann–Stacey domination argument, applied after renormalization into space-time blocks, shows that such a field dominates a supercritical independent percolation once the density of erased sites is small, that is, $\alpha$ small. Independence of the initial environment holds because the immune configuration started from all sites becomes indistinguishable from the one started from none after a finite time with exponential tail. Linear growth on survival uses restart arguments adapted to the renormalized, non-Markovian block process.

## Sources

- Olivier Garet, Régine Marchand, "Growth of a population of bacteria in a dynamical hostile environment", arXiv (2010). Section 1 (model, Theorems 1.1–1.2), Section 2 (Proposition 2.2, Theorem 2.5), Section 3 (Corollaries 3.1–3.3). <https://doi.org/10.48550/arXiv.1010.4618>. Published version: Advances in Applied Probability 46(3) (2014), 661–686, <https://doi.org/10.1239/aap/1409319554>; locators above refer to the arXiv version.
