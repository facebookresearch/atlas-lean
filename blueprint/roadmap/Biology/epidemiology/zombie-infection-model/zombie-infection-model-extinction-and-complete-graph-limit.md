# Zombie infection model: extinction threshold and complete-graph limit

**Model.** On a countable, connected, locally finite graph $G = (V,E)$ the zombie infection model (ZIM) is the Markov process on $\{S, I, R\}^V$ in which, for every edge $x \sim y$ with $x$ infected ($I$, a zombie) and $y$ susceptible:
- at rate $\lambda$ the zombie bites, $y \to I$;
- at rate $\mu$ the susceptible destroys the zombie, $x \to R$.

Removal therefore needs a susceptible neighbour, and a zombie with no susceptible neighbours stays infected forever. The law depends on $(\lambda,\mu)$ only through $\lambda/\mu$, so take $\mu = 1$. Start from a finite non-empty infected set $\Delta$ and no removed nodes; let $\mathcal{Z}_t$ be the number of zombies at time $t$ and $\phi(\lambda,G,\Delta) = \mathbb{P}(\mathcal{Z}_t \to \infty)$ the outbreak probability.

**Theorem (extinction).** If $\lambda \le 1$, then $\phi(\lambda, G, \Delta) = 0$ for every graph $G$ and finite $\Delta$.

**Theorem (complete graph).** On $K_N$ with $\Delta = \{1,\dots,M\}$, $M < N$ fixed, as $N \to \infty$

$$\frac{\mathcal{Z}_\infty}{N} \Rightarrow \begin{cases} 0, & \lambda \le 1,\\[2pt] \dfrac{\lambda - 1}{\lambda}\,X, \quad X \sim \operatorname{Bernoulli}\bigl(1 - \lambda^{-M}\bigr), & \lambda > 1. \end{cases}$$

## Expansion

Each event at an active edge raises the zombie count by one with probability $\lambda/(\lambda+1)$ and lowers it by one otherwise, so while susceptibles remain abundant $\mathcal{Z}$ is dominated by a simple random walk on $\mathbb{N}_0$ with that bias. For $\lambda \le 1$ the walk hits zero almost surely, which forces extinction on any graph (the same argument as for the biased voter model). On $K_N$ the walk started at $M$ escapes with gambler's-ruin probability $1 - \lambda^{-M}$; on escape the deterministic balance of bites and kills over the susceptible pool leaves a fraction $(\lambda-1)/\lambda$ of the population as zombies.

## Sources

- S. A. Bethuelsen, E. Broman, S. Modée, "The Zombie Infection Model" (2026), Section 2.1 (generator), Theorem 5 and Theorem 7, <https://doi.org/10.48550/arXiv.2607.29409>.
