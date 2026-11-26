# Goldreich–Goldwasser–Ron: bipartiteness is testable

Bipartiteness has a one-sided tester in the dense graph model with query complexity polynomial in $1/\varepsilon$ and independent of $n$: sample $s = O(\log(1/\varepsilon)/\varepsilon)$ vertices $U$ and $m = O(s/\varepsilon)$ further random pairs $(x_k, y_k)$, query all pairs between each $x_k, y_k$ and $U$ and the pairs $(x_k, y_k)$, and accept iff some 2-colouring of $U$ extends to all sampled pairs without a monochromatic queried edge. Bipartite graphs are always accepted, and graphs $\varepsilon$-far from bipartite are rejected with probability at least $2/3$.

## Proof sketch

Fix a partition of $U$. A graph $\varepsilon$-far from bipartite has, for every 2-colouring of all vertices, more than $\varepsilon n^2$ monochromatic edges. Colouring each sampled vertex by the side opposite to its neighbours in $U$ (which is forced, up to a few high-degree exceptions), a random pair is a violating edge with probability $\Omega(\varepsilon)$, and a union bound over the $2^s$ partitions of $U$ shows all are refuted.

## Depends on

- [Property testing in the dense graph model](dense-graph-property-testing-model.md)

## Sources

- O. Goldreich, S. Goldwasser and D. Ron, "Property Testing and Its Connection to Learning and Approximation", Journal of the ACM 45(4), 1998.
- O. Goldreich, "Introduction to Property Testing", Cambridge University Press, 2017.
