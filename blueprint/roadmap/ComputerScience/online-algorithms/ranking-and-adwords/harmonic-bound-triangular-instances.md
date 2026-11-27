# Harmonic upper bound for deterministic algorithms on permuted triangular instances

For $n \ge 1$ and a permutation $\sigma$ of $[n]$, let $\mathcal{T}_\sigma$ be the upper-triangular instance in which the $k$-th arriving vertex is adjacent to the offline vertices $\sigma(k), \sigma(k+1), \dots, \sigma(n)$; it has a perfect matching. For every deterministic online algorithm $A$ and every $0 \le s \le n$, the average over all $n!$ permutations $\sigma$ of the size of $A$'s matching on $\mathcal{T}_\sigma$ is at most $n - s(H_n - H_s)$, where $H_k$ is the $k$-th harmonic number.

## Proof sketch

Whatever $A$ does, the vertex it matches at step $k$ is the one the next arrival needs with probability depending only on how many candidates remain; a counting argument over $\sigma$ shows that after $n - s$ steps the expected number of usable remaining offline vertices drops as in the harmonic sum.

## Depends on

- [The RANKING algorithm](ranking-algorithm.md)

## Sources

- R. M. Karp, U. V. Vazirani and V. V. Vazirani, "An Optimal Algorithm for On-line Bipartite Matching", Proceedings of the 22nd ACM Symposium on Theory of Computing (STOC), 1990.
