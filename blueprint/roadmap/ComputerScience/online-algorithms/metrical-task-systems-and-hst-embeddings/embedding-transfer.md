# Competitive ratios transfer through dominating tree embeddings

Let $\mathcal{D}$ be a distribution over metrics $d_T$ on $M$ that dominate $d$ and have expected distortion at most $D$. Suppose there are constants $\alpha$ and $c$ such that for every $T$ in the support there is a randomized online algorithm $A_T$ for an MTS (or $k$-server) on $(M, d_T)$ with $\mathbb{E}[\mathrm{cost}_{d_T}(A_T, \sigma)] \le \alpha\, \mathrm{OPT}_{d_T}(\sigma) + c$ for every request sequence $\sigma$, with the same additive constant $c$ for all $T$ (automatic when $\mathcal{D}$ has finite support, by taking the largest of the per-tree constants, and with $c = 0$ when every $A_T$ is strictly $\alpha$-competitive). Then sampling $T \sim \mathcal{D}$ at the start and running $A_T$ gives a randomized algorithm on $(M, d)$ with expected cost at most $\alpha D\, \mathrm{OPT}_d(\sigma) + c$ on every $\sigma$, hence $\alpha D$-competitive against oblivious adversaries. The same holds with per-tree constants $c_T$ whenever $\mathbb{E}_T[c_T] < \infty$, with $c = \mathbb{E}_T[c_T]$; some such integrability is needed: if the algorithm for the $j$-th tree first wastes $j$ units of movement and $T_j$ has probability proportional to $1/j^2$, the expected start-up cost $\sum_j j \cdot \Theta(1/j^2)$ is infinite.

## Proof sketch

The algorithm's cost under $d$ is at most its cost under $d_T$ by domination, hence in expectation at most $\alpha\,\mathrm{OPT}_{d_T} + c$ with $c$ independent of $T$; and $\mathbb{E}_T[\mathrm{OPT}_{d_T}] \le \mathbb{E}_T[\mathrm{cost}_{d_T}(\text{the } d\text{-optimal solution})] \le D\,\mathrm{OPT}_d$, since the fixed $d$-optimal solution is oblivious to $T$.

## Depends on

- [Metrical task systems](metrical-task-system.md)
- [The k-server problem](../paging-and-k-server/the-k-server-problem.md)
- [Probabilistic embedding of a metric into dominating tree metrics](../../randomized-algorithms/sketching-streaming-and-sublinear-algorithms/johnson-lindenstrauss-optimality-and-metric-embeddings/probabilistic-embeddings-into-dominating-trees.md)

## Sources

- Yair Bartal, "Probabilistic Approximation of Metric Spaces and Its Algorithmic Applications", FOCS (1996).
- Jittat Fakcharoenphol, Satish Rao, Kunal Talwar, "A Tight Bound on Approximating Arbitrary Metrics by Tree Metrics", Journal of Computer and System Sciences 69(3) (2004).
