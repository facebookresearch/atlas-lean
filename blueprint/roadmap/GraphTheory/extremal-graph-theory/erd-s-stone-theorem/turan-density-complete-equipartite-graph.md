# Turán density of complete multipartite graphs

For $r \ge 1$ and every $t$,

$$\pi\big(K_{r+1}(t)\big) \le 1 - \frac{1}{r}.$$

Let $\delta > 0$. By the [Erdős–Stone theorem](eventually-complete-equipartite-graph-is.md), for large $n$ every graph on $n$ vertices without $K_{r+1}(t)$ has fewer than $(1 - 1/r + \delta)\, n^2/2$ edges. Hence $\mathrm{ex}(n, K_{r+1}(t))/\binom n2 \le (1 - 1/r + \delta)\, n/(n-1)$, which tends to $1 - 1/r + \delta$. Equality holds, by the [lower bound](one-sub-inv-le-turan-density.md), as soon as $t \ge 1$.

## Informally uses

- [Erdős–Stone theorem](eventually-complete-equipartite-graph-is.md): the edge bound for $K_{r+1}(t)$-free graphs.

## Sources

- J. Noel, *Extremal Combinatorics* lecture notes (version of 15 Nov 2026), extremalcombinatorics.com, proof of Theorem 3.3.10.
