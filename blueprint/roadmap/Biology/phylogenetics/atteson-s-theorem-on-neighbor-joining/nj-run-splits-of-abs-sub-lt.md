# Atteson's theorem: neighbor joining has sup-norm radius one half

Let $(G, \iota)$ be a [binary phylogenetic tree](../neighbor-joining/is-binary-phylogenetic-tree.md) on a finite set $X$ of taxa, with edge lengths $w_e > 0$, let $d(x, y)$ be the total length of the path from $\iota(x)$ to $\iota(y)$, and let $\mu \le w_{ab}$ for every internal edge $ab$ (neither endpoint a taxon vertex). Let $D$ be symmetric with $D(x, x) = 0$ and $|D(x, y) - d(x, y)| < \mu/2$ for all distinct taxa. Let a [run of neighbor joining](../neighbor-joining/njrun.md) on $D$ reach a cluster set $S$ with $|S| \le 3$, having formed the clusters $C$. Then for every set $A$ of taxa, $A \in C$ or $X \setminus A \in C$ if and only if there is an internal edge $ab$ such that $A$ is the set of taxa whose vertex is joined to $a$ after deleting the edge $ab$.

Atteson's theorem is classically stated with $\mu$ the minimum length of all edges, pendant edges included (Atteson 1999; Mihaescu, Levy and Pachter 2009, Theorem 2). The form above, which bounds only the internal edges, follows from it: adding a constant to all dissimilarities between one taxon and the others does not change the pairs that neighbor joining selects, so the pendant edges can be lengthened at will.

## Sources

- K. Atteson, *The performance of neighbor-joining methods of phylogenetic reconstruction*, Algorithmica 25 (1999), 251–278.
- R. Mihaescu, D. Levy and L. Pachter, *Why neighbor-joining works*, Algorithmica 54 (2009), 1–24; arXiv:cs/0602041, Theorem 2.
- The proof here is a new one, with the Studier–Keppler update of the cluster dissimilarities: up to row shifts, which do not change the pairs neighbor joining selects, the cluster dissimilarity of a run is an average of $D$, so its errors against the tree metric of the current clusters stay below $\mu/2$, and the cherry step applies at every join.
