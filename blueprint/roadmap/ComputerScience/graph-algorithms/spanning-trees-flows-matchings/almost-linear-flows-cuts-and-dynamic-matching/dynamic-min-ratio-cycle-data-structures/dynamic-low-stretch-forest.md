# Dynamic low-stretch forests with stable stretch overestimates

There is a deterministic algorithm with total running time $\widetilde{O}(m)$ that, given $G = (V, E)$ with lengths $\boldsymbol{\ell} > 0$, weights $\mathbf{v} > 0$ and a parameter $k$, initializes a low-stretch forest $(T, F, \widetilde{\mathrm{str}})$ together with an edge-disjoint partition $\mathcal{W}$ of $F$ into $O(m/k)$ subtrees, and maintains $F$ with a decremental edge set under $\tau$ batches of edge insertions, deletions and vertex splits, with $\widetilde{\mathrm{str}}_e = 1$ for inserted edges, such that with $q = \sum_{t \le \tau}|U^{(t)}| = \widetilde{O}(m)$:

1. $F$ has $O(m/k)$ components initially and $O(q\log^2 n)$ more after the updates;
2. $\mathrm{str}^{F, \boldsymbol{\ell}}_e \le \widetilde{\mathrm{str}}_e \le O(k\log^6 n)$ for every edge at all times, and $\widetilde{\mathrm{str}}_e$ never changes;
3. $\sum_{e \in E^{(0)}}\mathbf{v}_e\widetilde{\mathrm{str}}_e \le O(\|\mathbf{v}\|_1\log^4 n)$ for the initial edge set $E^{(0)}$;
4. every piece $W \in \mathcal{W}$ has at most one boundary vertex and $\mathrm{vol}_G(W \setminus R) \le O(k\log^2 n)$, where $R$ is the root set of $F$.

## Proof sketch

Compute a low-stretch spanning tree $T$ for weights $\mathbf{v}$ by *Abraham-Neiman low-stretch spanning trees via petal decompositions* and cut $T$ into $O(m/k)$ edge-disjoint subtrees of volume $O(k)$; making the boundary vertices roots of a forest $F \subseteq T$ costs an extra factor $O(k)$ in stretch only for edges crossing pieces, which is charged to the weight bound. Each update forces both endpoints of the affected edge (or the split vertex) to become roots, which removes $O(\log^2 n)$ edges from $F$ via a balanced decomposition of each piece and never increases the distance from a vertex to its root. Hence stretches only drop below the fixed overestimates and inserted edges have stretch $1$.

## Depends on

- [Stretch of an edge with respect to a rooted spanning forest](rooted-forest-edge-stretch.md)

## Proof depends on

- [Abraham-Neiman low-stretch spanning trees via petal decompositions](abraham-neiman-petal-lsst.md)

## Sources

- Jan van den Brand, Li Chen, Rasmus Kyng, Yang P. Liu, Richard Peng, Maximilian Probst Gutenberg, Sushant Sachdeva, Aaron Sidford, "A Deterministic Almost-Linear Time Algorithm for Minimum-Cost Flow", FOCS (2023), arXiv:2309.16629.
- Li Chen, Rasmus Kyng, Yang P. Liu, Richard Peng, Maximilian Probst Gutenberg, Sushant Sachdeva, "Maximum Flow and Minimum-Cost Flow in Almost-Linear Time", FOCS (2022), arXiv:2203.00671.
