# Compressed-sparse-row encoding of a directed graph

Let $G$ be a directed multigraph on vertices $\{0,\dots,n-1\}$ with $m$ arcs, optionally weighted by $c(e) \in \mathbb{N}$. Its **compressed-sparse-row (CSR) encoding** is the word sequence

$$
n,\; \mathrm{off}_0, \mathrm{off}_1, \dots, \mathrm{off}_n,\; t_0, c_0, t_1, c_1, \dots, t_{m-1}, c_{m-1},
$$

where $0 = \mathrm{off}_0 \le \mathrm{off}_1 \le \dots \le \mathrm{off}_n = m$, and the out-arcs of vertex $u$ are exactly the arcs $(u, t_j)$ of weight $c_j$ for $\mathrm{off}_u \le j < \mathrm{off}_{u+1}$. The encoding has $O(n + m)$ words, and the out-neighbours of any vertex can be enumerated in time proportional to its out-degree on a word RAM.

## Depends on

- [The word-RAM model](../../../TheoryOfComputation/fine-grained-complexity/fine-grained-hypotheses/the-word-ram-model.md)

## Sources

- T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, "Introduction to Algorithms", 3rd ed., MIT Press, 2009.
- R. E. Tarjan, "Data Structures and Network Algorithms", SIAM, 1983.
