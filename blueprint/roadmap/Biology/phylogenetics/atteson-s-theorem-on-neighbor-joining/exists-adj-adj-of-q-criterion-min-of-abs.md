# Robust cherry lemma for neighbor joining

Let $(G, \iota)$ be a [binary phylogenetic tree](../neighbor-joining/is-binary-phylogenetic-tree.md) on a finite set $X$ of at least four taxa, with edge lengths $w_e > 0$, and let $d(x, y)$ be the total length of the path from $\iota(x)$ to $\iota(y)$. Let $\mu$ satisfy $\mu \le w_{ab}$ for every internal edge $ab$ (neither endpoint a taxon vertex). Let $D$ be symmetric with $D(x, x) = 0$ and $|D(x, y) - d(x, y)| < \mu/2$ for all distinct taxa. If distinct taxa $x, y$ minimize the [Q-criterion](../neighbor-joining/q-criterion.md) of the [initial cluster dissimilarity](../neighbor-joining/initial-dist.md) of $D$ over all pairs of distinct singleton clusters, then $\iota(x)$ and $\iota(y)$ have a common neighbour: they form a cherry (Atteson 1999; proof after Mihaescu, Levy & Pachter 2009, Theorem 16).

## Sources

- K. Atteson, *The performance of neighbor-joining methods of phylogenetic reconstruction*, Algorithmica 25 (1999), 251–278.
- R. Mihaescu, D. Levy and L. Pachter, *Why neighbor-joining works*, Algorithmica 54 (2009), 1–24; arXiv:cs/0602041, Theorem 16.
