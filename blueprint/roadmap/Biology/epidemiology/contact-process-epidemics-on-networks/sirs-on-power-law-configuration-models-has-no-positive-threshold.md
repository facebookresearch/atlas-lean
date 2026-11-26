# SIRS epidemics on power-law configuration models have no positive threshold

**Model.** Fix $\tau > 2$ and let $G(n,\tau)$ be the configuration model on $n$ vertices with i.i.d. degrees $\mathbb{P}(D = k) = C_\tau k^{-\tau}\mathbf{1}\{k \ge 3\}$ (half-edges paired uniformly; multigraph allowed). The process $\mathrm{SIRS}(G, \lambda, \rho)$ is the continuous-time Markov chain on $\{S, I, R\}^V$ in which
- each infected vertex infects each susceptible neighbor at rate $\lambda > 0$;
- each infected vertex recovers ($I \to R$) at rate $1$;
- each recovered vertex loses immunity ($R \to S$) at rate $\rho > 0$.

$\rho = \infty$ gives SIS (the contact process) and $\rho = 0$ gives SIR. Let $T$ be the extinction time of the infection.

**Theorem.** Fix $\lambda, \rho > 0$, $\delta \in (0,1)$ and $\tau > 2$.
1. Starting from all vertices infected, $\mathbb{P}\big(T \ge \exp(n^{1-\delta})\big) \to 1$ as $n \to \infty$, under the joint law of the graph and the epidemic.
2. There is $p = p(\lambda, \rho, \tau, \delta) > 0$ such that, if an arbitrary initial configuration (any law $\mu_n$ on $\{S,I,R\}^V$) is modified by infecting one uniformly chosen vertex, then for all large $n$

$$\inf_{\mu_n} \mathbb{P}^*_{\mu_n}\big(T \ge \exp(n^{1-\delta})\big) \ge p.$$

So, as for SIS (Chatterjee–Durrett), the critical infection rate separating polynomial from stretched-exponential survival is $0$ for every waning rate $\rho > 0$, contradicting mean-field predictions of a positive SIRS threshold on scale-free networks.

**Key structural input.** With $\varepsilon = \delta/(400\tau^3)$, with probability at least $1 - c(\log n)^{\mathbf{1}\{\tau = 3\}} n^{-\min\{\tau - 2, 1\}}$ the graph contains at least $\lceil n^{1-\delta}\rceil$ vertex-disjoint $(n^\varepsilon, n^\varepsilon)$-**hierarchical stars**: a center joined to $n^\varepsilon$ hubs, each itself the center of a star with $n^\varepsilon$ leaves. On any graph with that many disjoint hierarchical stars and diameter $O(\log n)$, SIRS from all-infected survives for time $\exp(n^{1-\delta})$ with probability at least $1 - \exp(-n^{1-\delta})$.

## Expansion

On a single star of degree $k$, SIS survives for time $e^{ck}$ because the hub reinfects leaves faster than they recover. Under SIRS the hub itself enters the immune state for an $\mathrm{Exp}(\rho)$ time, during which its leaves clear, so a lone star is not enough. A hierarchical star fixes this: while the top center is immune, enough second-level hubs remain lit (a positive fraction of their leaves infected) to reinfect it once it becomes susceptible, and the second-level hubs keep each other alive through the center. Because SIRS lacks attractiveness, survival on a subgraph does not transfer by monotone coupling; the proof instead builds explicit good events measurable with respect to the Poisson clocks of each hierarchical star and chains $n^{1-\delta}$ disjoint stars through short paths.

## Sources

- Zihao He, Souvik Dhara and Debankur Mukherjee, "Waning Immunity Fails to Restore a Positive Epidemic Threshold on Power-Law Networks", arXiv:2604.24684 (2026), Section 2 (model and Theorems 2.1–2.2), Propositions 3.3, 4.4, 5.1 and 6.3, <https://doi.org/10.48550/arXiv.2604.24684>.
