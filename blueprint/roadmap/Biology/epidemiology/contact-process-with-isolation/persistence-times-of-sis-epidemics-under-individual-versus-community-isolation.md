# Persistence times of SIS epidemics under individual versus community isolation

**Models.** On a finite graph $G=(V,E)$ with $|V|=n$, each vertex is healthy ($0$), infected ($1$) or isolated ($-1$). An infected vertex infects each healthy neighbour at rate $\lambda$; infected and isolated vertices return to healthy at rate $1$. Isolated vertices neither transmit nor receive infection.
- *Contact process with isolation:* each infected vertex self-isolates at rate $\alpha$.
- *Contact process with vigilance:* each infected vertex is isolated at rate $\alpha$ times its number of healthy neighbours.
Let $\tau$ be the extinction time of infection, started from all vertices infected. Neither process is known to be attractive (monotone in the initial infected set).

**Theorem (individual isolation cannot stop persistence on heavy-tailed graphs).** Let $G$ be a configuration-model graph with i.i.d. degrees $D_i \ge 3$, $\mathbb{P}(D_i \ge k) \asymp k^{-(\gamma-1)}$, $\gamma > 3$. For every $\alpha, \lambda, \eta > 0$, the contact process with isolation satisfies $\mathbb{P}(\tau < e^{n^{1-\eta}}) \to 0$. The same holds for the SIRS process in which infected vertices gain temporary immunity at rate $\alpha$ and lose it at rate $1$.

**Theorem (vigilance gives a phase transition).**
1. On *any* graph, if $\lambda < \alpha$ then there is $C>0$ with $\mathbb{P}(\tau > Cn) \to 0$.
2. If $G$ is an expander on mid-sized sets, i.e. there are $0 < \epsilon' < \epsilon < 1/2$ and $\delta > 0$ with $|\partial B| \ge \delta|B|$ whenever $\epsilon' n \le |B| \le \epsilon n$, then there are $\lambda_0(\alpha,\epsilon,\delta)$ and $C>0$ such that for $\lambda > \lambda_0$, $\mathbb{P}(\tau < e^{Cn}) \to 0$.
3. The power-law configuration model above ($\gamma > 3$) satisfies this expansion property with probability $1-o(1)$, so on it vigilance yields short survival for $\lambda < \alpha$ and exponentially long survival for large $\lambda$.

## Depends on

- [Spectral radius and die-out of SIS epidemics](../epidemics-on-networks/spectral-radius-and-die-out-of-sis-epidemics.md)

## Expansion

With self-isolation, an infected high-degree vertex (a star) still recovers and is reinfected by its many leaves, isolation only reducing the effective infection rate by a constant factor; stars connected through short paths pass the infection back and forth, so survival is at least $\exp(n^{1-\eta})$ exactly as for the classical contact process on power-law graphs. With vigilance, an infected vertex with $h$ healthy neighbours is removed at rate $\alpha h$ while it infects at rate at most $\lambda h$, so when $\lambda < \alpha$ every infected vertex is more likely to be isolated than to infect, and the infected count is dominated by a subcritical process: high degree now helps containment. For large $\lambda$, expansion guarantees that a linear-size infected set keeps a linear boundary, giving a drift argument for exponential survival despite the lack of attractiveness.

## Sources

- Shirshendu Chatterjee, David Sivakoff, Matthew Wascher, "The effects of individual versus community-influenced isolation on SIS epidemic persistence on finite random graphs", arXiv:2512.06175 (2025), Assumptions 1–2, Theorems 1–4 and Corollaries 1–2, <https://doi.org/10.48550/arXiv.2512.06175>.
