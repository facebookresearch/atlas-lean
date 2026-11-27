# Replicable heavy hitters with domain-independent sample complexity

A randomized algorithm $A(S; r)$ taking an i.i.d. sample $S$ from a distribution $D$ and internal randomness $r$ is **$\rho$-replicable** if $\Pr_{S, S' \sim D^n,\, r}[A(S; r) = A(S'; r)] \ge 1 - \rho$ for every $D$, where $S, S', r$ are independent and the same $r$ is used in both runs. For a distribution $D$ on a countable set $X$, call $x$ a $v$-heavy hitter if $D(\{x\}) \ge v$. For all $\varepsilon \in (0, 1/2)$ and $v \in (\varepsilon, 1 - \varepsilon)$ there is a $\rho$-replicable algorithm that, with probability at least $1 - \rho$, outputs the set of $v'$-heavy hitters of $D$ for some $v' \in [v - \varepsilon, v + \varepsilon]$ (chosen from the shared randomness), using

$$
\tilde O\!\left(\frac{1}{\rho^2 \varepsilon^2 (v - \varepsilon)^2}\right)
$$

samples, independent of $|X|$. In contrast, every statistical query algorithm for the heavy-hitters problem that uses queries of tolerance $\tau$ needs $\Omega(\log |X| / \log(1/\tau))$ queries, so replicable algorithms are strictly more powerful than statistical query algorithms.

## Proof sketch

A first batch of samples contains every $(v-\varepsilon)$-heavy hitter with high probability; for each candidate, estimate its mass replicably and keep it if the estimate exceeds the random threshold $v'$. Choosing $v'$ uniformly in $[v - \varepsilon, v + \varepsilon]$ makes it unlikely that any true mass is within the estimation error of $v'$, so both runs keep the same candidates. The statistical query lower bound uses the family of point masses $D_x$: each query distinguishes few of them, and $|X|$ alternatives require $\log|X|/\log(1/\tau)$ queries.

## Depends on

- [Replicable algorithms with shared randomness](../../../replicable-learning/replicable-algorithms-with-shared-seed.md)

## Proof depends on

- [Replicable simulation of a statistical query by randomized rounding](replicable-statistical-query-simulation.md)

## Sources

- R. Impagliazzo, R. Lei, T. Pitassi, J. Sorrell, "Reproducibility in Learning", STOC (2022), arXiv:2201.08430, Definitions 3.1 and 3.2, Lemma 3.3 and Claim 3.5.
