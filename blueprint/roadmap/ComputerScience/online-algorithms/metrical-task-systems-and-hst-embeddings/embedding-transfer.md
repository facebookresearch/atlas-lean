# Competitive ratios transfer through dominating tree embeddings

Let $\mathcal{D}$ be a distribution over metrics $d_T$ on $M$ that dominate $d$ and have expected distortion at most $D$. If for every $T$ in the support there is an $\alpha$-competitive randomized online algorithm for an MTS (or $k$-server) on $(M, d_T)$, then sampling $T \sim \mathcal{D}$ at the start and running that algorithm gives an $\alpha D$-competitive randomized algorithm on $(M, d)$ against oblivious adversaries.

## Proof sketch

The algorithm's cost under $d$ is at most its cost under $d_T$ by domination, hence at most $\alpha\,\mathrm{OPT}_{d_T} + c$; and $\mathbb{E}_T[\mathrm{OPT}_{d_T}] \le \mathbb{E}_T[\mathrm{cost}_{d_T}(\text{the } d\text{-optimal solution})] \le D\,\mathrm{OPT}_d$, since the fixed $d$-optimal solution is oblivious to $T$.

## Depends on

- [Metrical task systems](metrical-task-system.md)
- [The k-server problem](../paging-and-k-server/the-k-server-problem.md)
- [Probabilistic embedding of a metric into dominating tree metrics](../../randomized-algorithms/sketching-streaming-and-sublinear-algorithms/johnson-lindenstrauss-optimality-and-metric-embeddings/probabilistic-embeddings-into-dominating-trees.md)

## Sources

- Yair Bartal, "Probabilistic Approximation of Metric Spaces and Its Algorithmic Applications", FOCS (1996).
- Jittat Fakcharoenphol, Satish Rao, Kunal Talwar, "A Tight Bound on Approximating Arbitrary Metrics by Tree Metrics", Journal of Computer and System Sciences 69(3) (2004).
