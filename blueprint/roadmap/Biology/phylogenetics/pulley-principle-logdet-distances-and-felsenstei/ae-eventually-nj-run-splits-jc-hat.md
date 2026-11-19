# Consistency of neighbor joining under Jukes–Cantor given a recovery radius

Let $(G, \iota)$ be a [binary phylogenetic tree](../neighbor-joining/is-binary-phylogenetic-tree.md) on a finite set $X$ with real edge lengths $w$ and path metric $d$, let $\mu$ be real and $r > 0$ such that neighbor joining [recovers the tree within radius](njrecovers-within.md) $r$ of $\mu d$. Let $P$ be a probability measure and the sites $\mathrm{site}_0, \mathrm{site}_1, \dots$ measurable, pairwise independent and identically distributed, with $\Pr(\mathrm{site}_0(x) = i, \mathrm{site}_0(y) = j) = \frac14 M_{ij}$ for every path from $\iota(x)$ to $\iota(y)$, where $M$ is the [path matrix](jc-path.md) of its edge lengths. Then almost surely, for all sufficiently large $n$, every run of neighbor joining on the [corrected empirical distances](jc-hat.md) of the first $n$ sites reaching at most three clusters forms exactly the splits of the internal edges of the tree (Saitou & Nei 1987; Atteson 1999).

## Sources

- N. Saitou and M. Nei, *The neighbor-joining method: a new method for reconstructing phylogenetic trees*, Mol. Biol. Evol. 4 (1987), 406–425.
- K. Atteson, *The performance of neighbor-joining methods of phylogenetic reconstruction*, Algorithmica 25 (1999), 251–278.
