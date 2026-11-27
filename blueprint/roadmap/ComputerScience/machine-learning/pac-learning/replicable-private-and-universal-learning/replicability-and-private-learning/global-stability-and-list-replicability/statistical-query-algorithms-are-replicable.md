# Every statistical query algorithm has a replicable implementation

A randomized algorithm $A(S; r)$ taking an i.i.d. sample $S$ from a distribution $D$ and internal randomness $r$ is **$\rho$-replicable** if $\Pr_{S, S' \sim D^n,\, r}[A(S; r) = A(S'; r)] \ge 1 - \rho$ for every $D$, where $S, S', r$ are independent and the same $r$ is used in both runs. Let $\mathcal{A}$ be an algorithm that makes at most $q$ statistical queries of tolerance $\tau$ (adaptively) and otherwise uses only its own coins. Then $\mathcal{A}$ can be simulated from i.i.d. samples by a $\rho$-replicable algorithm with the same output guarantees except for an additional failure probability $\delta$, using $\tilde O\big(q^3 / (\tau^2 \rho^2)\big)$ samples in total (answering each query on fresh samples with replicability parameter $\rho/q$). Consequently replicable algorithms exist for approximate medians, heavy hitters, learning conjunctions and every concept class learnable from statistical queries.

## Proof sketch

Answer the $j$-th query with the replicable rounding procedure at replicability level $\rho/q$ using shared randomness $r_j$ and fresh samples. If two runs agree on the answers to the first $j-1$ queries, they ask the same $j$-th query, and the answers agree except with probability $\rho/q$; a union bound over the $q$ queries gives $\rho$-replicability, and each query costs $\tilde O(q^2/(\tau^2\rho^2))$ samples.

## Proof depends on

- [Replicable simulation of a statistical query by randomized rounding](replicable-statistical-query-simulation.md)
- [Statistical-query learning implies noise-tolerant PAC learning](../../../statistical-query-learning-implies-noise-tolerant-pac-learni.md)

## Sources

- R. Impagliazzo, R. Lei, T. Pitassi, J. Sorrell, "Reproducibility in Learning", STOC (2022), arXiv:2201.08430.
