# Turán density of complete graphs

Turán's theorem says that among graphs on $n$ vertices with no complete subgraph $K_{r+1}$, the Turán graph $T(n, r)$ (the complete $r$-partite graph with parts as equal as possible) has the most edges, so the extremal number of $K_{r+1}$ is the number of edges $t(n, r)$ of $T(n, r)$, and $2r\,t(n, r) \le (r-1)n^2$. The Turán density is $\pi(H) = \lim_n \mathrm{ex}(n, H)/\binom{n}{2}$. A matching [lower bound on the Turán number](turan-number-lower-bound.md), from the recursion $t(n + r, r) = t(n, r) + n(r-1) + \binom{r}{2}$, gives the [Turán density of complete graphs](turan-density-complete-graph.md), $\pi(K_{r+1}) = 1 - 1/r$.

For $r = 2$ this is Mantel's density $\pi(K_3) = 1/2$; [Goodman's bound](../triangle-density-and-flag-algebras/goodman.md) proves the finite form $4m \le n^2$ the flag-algebra way. By the [Erdős–Stone–Simonovits theorem](../erd-s-stone-theorem/README.md), every graph $H$ of chromatic number $r + 1$ has the same density $1 - 1/r$, derived there from the minimum-degree form of the Erdős–Stone theorem.

- [Lower bound on the Turán number](turan-number-lower-bound.md)
- [Turán density of complete graphs](turan-density-complete-graph.md)
- [Cliques in multipartite graphs](cliques-in-multipartite-graphs/README.md)
- [Graphs just above the Turán threshold](graphs-just-above-the-tur-n-threshold/README.md)

## Related topics

- [Triangle density and flag algebras](../triangle-density-and-flag-algebras/README.md): Mantel's theorem from Goodman's bound, and the minimum number of triangles above the Mantel threshold.
- [Generalized Turán numbers](../generalized-tur-n-numbers/README.md): the largest number of copies of one graph in a graph avoiding another.
- [Erdős–Stone theorem](../erd-s-stone-theorem/README.md): the density $1 - 1/(\chi(H) - 1)$ of every graph $H$ with an edge, which reduces to the complete case.
