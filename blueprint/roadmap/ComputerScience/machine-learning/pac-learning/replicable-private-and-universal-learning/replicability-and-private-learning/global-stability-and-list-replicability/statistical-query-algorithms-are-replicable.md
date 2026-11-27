# Every statistical query algorithm has a replicable implementation

A randomized algorithm $A(S; r)$ taking an i.i.d. sample $S$ from a distribution $D$ and internal randomness $r$ is **$\rho$-replicable** if $\Pr_{S, S' \sim D^n,\, r}[A(S; r) = A(S'; r)] \ge 1 - \rho$ for every $D$, where $S, S', r$ are independent and the same $r$ is used in both runs. Let $\mathcal{A}$ be an algorithm that makes at most $q$ statistical queries of tolerance $\tau$ (adaptively) and otherwise uses only its own coins. Then $\mathcal{A}$ can be simulated from i.i.d. samples by a $\rho$-replicable algorithm with the same output guarantees except for an additional failure probability $\delta$, using $\tilde O\big(q^3 / (\tau^2 \rho^2)\big)$ samples in total (answering each query on fresh samples with replicability parameter $\rho/q$). Consequently every concept class learnable from polynomially many statistical queries of inverse-polynomial tolerance has a replicable learner with polynomial sample complexity.

## Proof sketch

Answer the $j$-th query $\psi_j : X \to [0,1]$ by replicable bounded-mean estimation of $\mathbb{E}_D[\psi_j]$ at replicability level $\rho/q$, with grid width $w = \tau$, deviation $t = \tau\rho/(6q)$, shift range $N \ge 3q/\rho$, shared randomness $r_j$ and fresh samples; the rounding moves the estimate by at most $\tau/2$, and Hoeffding's inequality sets the sample size. If two runs agree on the answers to the first $j-1$ queries, they ask the same $j$-th query, and the answers agree except with probability $\rho/q$; a union bound over the $q$ queries gives $\rho$-replicability, and each query costs $\tilde O(q^2/(\tau^2\rho^2))$ samples.

## Depends on

- [Replicable algorithms with shared randomness](../../../replicable-learning/replicable-algorithms-with-shared-seed.md)
- [Statistical query model with tolerance and the SQ dimension](../../../statistical-query-dimension/statistical-query-dimension.md)

## Proof depends on

- [Replicable bounded-mean and coin-bias estimation](../../../replicable-learning/replicable-mean-estimation.md)
- [Composition of replicable algorithms](../../../replicable-learning/composition-of-replicable-algorithms.md)

## Sources

- R. Impagliazzo, R. Lei, T. Pitassi, J. Sorrell, "Reproducibility in Learning", STOC (2022), arXiv:2201.08430, Definitions 1.1, 2.1 and 2.2, Theorem 2.3 and the adaptive-composition statement in Section 1.1 and Appendix A.
