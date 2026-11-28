# Every statistical query algorithm has a replicable implementation

A randomized algorithm $A(S; r)$ taking an i.i.d. sample $S$ from a distribution $D$ and internal randomness $r$ is **$\rho$-replicable** if $\Pr_{S, S' \sim D^n,\, r}[A(S; r) = A(S'; r)] \ge 1 - \rho$ for every $D$, where $S, S', r$ are independent and the same $r$ is used in both runs. A statistical query oracle for $D$ with tolerance $\tau \in [0,1]$ answers a query $\phi : X \to [0,1]$ with some $v$ satisfying $|v - \mathbb{E}_{x \sim D}[\phi(x)]| \le \tau$; a routine run on an i.i.d. sample from $D$ simulates it with failure rate $\delta$ if its answer satisfies this inequality except with probability $\delta$. Let $\tau, \delta, \rho \in [0,1]$ with $\rho > 2\delta$. The routine that computes the empirical mean of $\phi$ on its sample and returns the midpoint of the cell containing it, in a partition of $[0,1]$ into intervals of width $\alpha = 2\tau/(\rho + 1 - 2\delta)$ shifted by a uniformly random offset in $[0, \alpha]$ drawn from its internal randomness, $\rho$-replicably simulates the statistical query oracle with tolerance $\tau$ for $\phi$ with failure rate $\delta$, using a sample of size

$$
\tilde O\Big(\frac{1}{\tau^2(\rho - 2\delta)^2}\Big).
$$

Consequently every statistical query algorithm can be made replicable with a modest increase in sample complexity, by answering its queries in turn on fresh samples with this routine.

## Proof sketch

Let $\tau' = \tau(\rho - 2\delta)/(\rho + 1 - 2\delta)$, so that $\alpha/2 + \tau' = \tau$ and $2\tau'/\alpha = \rho - 2\delta$. By a Chernoff bound, $O(\log(1/\delta)/\tau'^2)$ samples put the empirical mean within $\tau'$ of $\mathbb{E}_D[\phi]$ except with probability $\delta$, and then the returned midpoint is within $\alpha/2 + \tau' = \tau$ of it. In two runs with the same offset and independent samples, both empirical means are within $\tau'$ of the expectation except with probability $2\delta$, and two points at distance at most $2\tau'$ fall into different cells with probability at most $2\tau'/\alpha = \rho - 2\delta$ over the offset, so the runs agree except with probability $\rho$. For a whole statistical query algorithm, if two runs agree on the answers to the first $j - 1$ queries they ask the same $j$-th query, so splitting the replicability and failure budgets over the queries and taking a union bound gives a replicable simulation.

## Depends on

- [Replicable algorithms with shared randomness](../../../replicable-learning/replicable-algorithms-with-shared-seed.md)
- [Statistical query model with tolerance and the SQ dimension](../../../statistical-query-dimension/statistical-query-dimension.md)

## Proof depends on

- [Replicable bounded-mean and coin-bias estimation](../../../replicable-learning/replicable-mean-estimation.md)
- [Composition of replicable algorithms](../../../replicable-learning/composition-of-replicable-algorithms.md)

## Sources

- R. Impagliazzo, R. Lei, T. Pitassi, J. Sorrell, "Reproducibility in Learning", STOC (2022), arXiv:2201.08430, Definitions 1.1, 2.1 and 2.2, Algorithm 1, Theorem 2.3 and the abstract.
