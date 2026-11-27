# Spectral expanders have large cut rank across balanced cuts

Let $G$ be a simple $d$-regular graph on $n$ vertices (no loops or parallel edges) with normalized spectral expansion $\mu$, and for $S \subseteq V$ let $\operatorname{cutrank}(S)$ be the rank, over a field $\mathbb{K}$, of the $S \times (V \setminus S)$ submatrix of the adjacency matrix. Tanner's estimate says every $s$-element set has at least $s n / (s + \mu^2 (n - s))$ neighbours. Consequently, over every field and for every $S$ with $|S| = s$,

$$(1 - \mu^2)\, s\,(n - s) \le d \cdot \operatorname{cutrank}(S)\cdot\bigl(s + \mu^2 (n - s)\bigr).$$

In particular, if $d = 7$ and $\mu \le 7/10$, every cut with $n/3 \le |S| \le 2n/3$ has $\operatorname{cutrank}(S) \ge n/41$.

## Proof sketch

The sharp mixing lemma applied to $S$ and the complement of its neighbourhood gives Tanner's estimate. The exterior neighbours of $S$ are covered by the neighbourhoods of the vertices indexing a row basis of the cut matrix, each contributing at most $d$ vertices; so the number of exterior neighbours, bounded below by Tanner's estimate, is at most $d\cdot\operatorname{cutrank}(S)$. The cut matrix of $V \setminus S$ is the transpose of that of $S$, so $\operatorname{cutrank}(S) = \operatorname{cutrank}(V \setminus S)$ and one may assume $n/3 \le s \le n/2$; plugging in $d = 7$ and $\mu \le 7/10$ on that range gives $41$ (directly at $s = 2n/3$ the bound only guarantees $n/52$).

## Depends on

- [Spectral expansion, second eigenvalue and edge expansion of a regular multigraph](../../graph-families-and-operations/expander-graph-operations/spectral-expansion-second-eigenvalue-and-edge-expansion.md)

## Proof depends on

- [Expander mixing lemma](../../graph-families-and-operations/expander-graphs/expander-mixing-lemma.md)

## Sources

- S. Hoory, N. Linial, A. Wigderson, "Expander Graphs and Their Applications", Bulletin of the American Mathematical Society, 2006.
- C. Lee, J. Lee, S. Oum, "Rank-width of Random Graphs", Journal of Graph Theory, 2012.
