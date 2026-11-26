# Law of large numbers for the SIR epidemic on a dynamic Erdős–Rényi graph

**Model.** On $n$ vertices, each absent edge appears at rate $\lambda_n$ and each present edge disappears at rate $\mu_n$, independently of everything else, so the graph process is stationary with the Erdős–Rényi law $G(n, \lambda_n/(\lambda_n + \mu_n))$. Start the graph in equilibrium and infect one uniformly chosen vertex. Each infected vertex infects each current neighbour at rate $\beta_n$ and recovers (permanently immune) at rate $\gamma$. Parameters scale as $\beta_n = \beta n^{\kappa_\beta}$, $\mu_n = \mu n^{\kappa_\mu}$, $\lambda_n = \lambda n^{\kappa_\lambda}$ with fixed $\beta, \mu, \lambda, \gamma > 0$.

**Theorem.** Let $S_n, I_n, R_n$ be the numbers of susceptible, infected and recovered vertices. There are random time shifts $\tau_n$, deterministic time changes $t_n(u)$, and events $A_n$ with $\liminf_n \mathbb{P}(A_n) > 0$ contained in the event of a major outbreak, such that for every $\varepsilon > 0$ and $T \in \mathbb{R}$
$$
\lim_{n\to\infty} \mathbb{P}\Bigl(\sup_{u \le T} \bigl| n^{-1} S_n(\tau_n + t_n(u)) - s(u) \bigr| > \varepsilon \,\Bigm|\, A_n\Bigr) = 0,
$$
and likewise for $n^{-1}I_n \to i$ and $n^{-1}R_n \to r$. The limit has the form $s(u) = \mathbb{E}\exp(-\widehat W e^{\widehat{\mathcal{M}} u})$ for a random variable $\widehat W$ and Malthusian parameter $\widehat{\mathcal{M}}$ of the approximating branching process. In most scaling regimes $(s, i, r)$ solve the classical SIR equations with an effective reproduction ratio depending on $\beta, \lambda, \mu$. In the regime $\kappa_\mu = 0$, $\kappa_\lambda = -1$, $\kappa_\beta = 0$ (bounded mean degree, edges turning over on the epidemic time scale) they solve instead
$$
s' = -\beta\,l\,s, \qquad i' = \beta\,l\,s - \gamma i, \qquad r' = \gamma i, \qquad
l' = \frac{\beta\lambda}{\mu}\, l\, s + \lambda i - (\beta + \mu + \gamma)\, l,
$$
with $s + i + r = 1$. The same conclusions hold for the multi-type version on a dynamic stochastic block model.

## Depends on

- [Final-size equation (Kermack–McKendrick 1927)](../kermack-mckendrick-sir-model/final-size-eq.md)

## Expansion

Early on, the epidemic seen from a fixed susceptible vertex is a branching process in which each infected individual's contacts form a point process shaped by the edge dynamics; the epidemic proper is coupled to a forward branching process, and the susceptibility set of a typical vertex to a backward one, until they meet. After the random shift that aligns the start of exponential growth, each vertex escapes infection with probability $\mathbb{E}\exp(-\widehat W e^{\widehat{\mathcal{M}}u})$, which gives $s$. In the bounded-degree, fast-turnover regime the infection pressure is carried by the auxiliary quantity $l$, which tracks connections from infected to susceptible vertices: such edges are created at rate $\lambda$ per infected vertex, used up by transmission and recovery, and broken at rate $\mu$, which yields the fourth equation.

## Sources

- Y. Huang, A. Röllin, "The SIR epidemic on a dynamic Erdős-Rényi random graph", arXiv:2404.12566 (2024), Section 1 (single-type outline and ODE system for case 6b), Theorems 2.3, 2.4, 2.7 and 3.3, <https://doi.org/10.48550/arXiv.2404.12566>.
