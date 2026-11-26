# Invasion-rate threshold for a switching stochastic flocculation model

**Model.** Nutrient $S$, microorganisms $X$ and flocculant $P$ in a chemostat-type reactor evolve as
$$\begin{aligned}
dS &= \big[D(\xi_t)(S_0-S) - \mu_1(\xi_t)SX\big]dt + \sigma_1 S\,dW_1,\\
dX &= \big[\mu_2(\xi_t)SX - D(\xi_t)X - h_2(\xi_t)XP\big]dt + \sigma_2 X\,dW_2,\\
dP &= \big[D(\xi_t)(P_0-P) - h_3(\xi_t)XP\big]dt + \sigma_3 P\,dW_3,
\end{aligned}$$
where $W_1,W_2,W_3$ are independent Brownian motions and $\xi_t$ is an irreducible Markov chain on a finite set $\mathcal{M}$ of environmental regimes (dilution rate $D$, inputs $S_0,P_0$, uptake $\mu_1$, growth $\mu_2$, flocculation rates $h_2,h_3$). For every positive initial condition there is a unique global positive solution, and $X\equiv0$ is invariant. On $\{X=0\}$ the process $(S,P,\xi)$ has a unique invariant probability measure $\mu_b$ on $\mathbb{R}^2_{>0}\times\mathcal{M}$.

**Theorem.** Let $\Lambda$ be the invasion rate of the microorganisms, i.e. the long-run average of the per-capita growth rate of $\log X$ near $X=0$,

$$\Lambda = \sum_{k\in\mathcal{M}}\int \Big(\mu_2(k)s - D(k) - h_2(k)p - \frac{\sigma_2^2}{2}\Big)\,\mu_b(ds\,dp,k).$$

1. If $\Lambda<0$, then for every positive initial condition $\lim_{t\to\infty}\frac1t\ln X(t)=\Lambda$ almost surely: the microorganisms go extinct exponentially fast.
2. If $\Lambda>0$, there is an invariant probability measure $\mu^\circ$ on $\mathbb{R}^3_{>0}\times\mathcal{M}$ and $q>1$ such that $t^{q-1}\|P_t((y,k),\cdot)-\mu^\circ\|_{TV}\to0$ for every positive initial state: the population persists and converges in total variation to a unique stationary distribution at a polynomial rate.

## Expansion

When $X$ is small, $S$ and $P$ follow the microbe-free dynamics with stationary law $\mu_b$, and Itô's formula gives $d\log X = (\mu_2S - D - h_2P - \sigma_2^2/2)dt + \sigma_2dW_2$; the ergodic theorem then shows that $\frac1t\log X$ approaches $\Lambda$. A Lyapunov function combining moment bounds with $X^{-\delta}$ handles $\Lambda>0$, and the extinction case requires showing that trajectories started near the boundary stay close to it with high probability. Without noise and switching this recovers the deterministic threshold $\mu_2S_0 \gtrless h_2P_0 + D$.

## Sources

- A. Hening, N. T. Hieu, D. H. Nguyen, N. Nguyen, "Dynamics of stochastic microorganism flocculation models", arXiv:2511.12975, Theorem 1.1, Corollary 1.2 and Theorems 1.3–1.4. <https://doi.org/10.48550/arXiv.2511.12975>
