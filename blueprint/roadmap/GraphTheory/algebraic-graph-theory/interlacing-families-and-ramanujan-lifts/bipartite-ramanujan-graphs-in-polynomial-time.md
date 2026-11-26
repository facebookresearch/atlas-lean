# Cohen: bipartite Ramanujan graphs of all degrees and sizes in polynomial time

There is a deterministic algorithm that, given $d \ge 3$ and $n$, outputs a $d$-regular bipartite Ramanujan multigraph with $n$ vertices per side in time $\mathrm{poly}(n, d)$.

## Proof sketch

Use a shallow interlacing family over unions of $d$ perfect matchings: a node is a sequence of matchings in which all but the last are complete and the last matches a prefix of the left vertices, and its children extend the partial matching by one vertex (or start the next matching). The polynomial attached to a node is the expected characteristic polynomial of the uniformly random completion **divided by the trivial factor** $x^2 - d^2$; the full characteristic polynomial always has the root $d > 2\sqrt{d-1}$, so only this reduced polynomial can be compared with the Ramanujan threshold. At the root it is the reduced expected polynomial of the union of $d$ random matchings, whose largest root is at most $2\sqrt{d-1}$, and siblings have a common interlacing, so some child's reduced polynomial has largest root at most its parent's. The algorithm walks down the tree. It computes each child's reduced polynomial exactly, with rational coefficients of polynomial bit length, by reducing the expected characteristic polynomial of a graph plus a random matching to a linear formula in the characteristic polynomial of the graph. It then tests exactly whether the largest root is at most $\sqrt{q}$ for $q = 4(d-1)$: shift to $p(x + \sqrt{q})$ over $\mathbb{Q}[\sqrt{q}]$ and check that all coefficients are nonnegative, which characterizes real-rooted polynomials with all roots at most $0$. The leaf reached has nontrivial eigenvalues at most $2\sqrt{d-1}$, and by bipartite symmetry it is Ramanujan.

## Depends on

- [Ramanujan graphs and bipartite Ramanujan graphs](ramanujan-graphs-and-bipartite-ramanujan-graphs.md)

## Proof depends on

- [Marcus-Spielman-Srivastava: bipartite Ramanujan graphs of every degree and every size](bipartite-ramanujan-graphs-of-all-sizes.md)

## Sources

- Michael B. Cohen, "Ramanujan graphs in polynomial time", FOCS (2016); arXiv:1604.03544 (Sections 2-4).
