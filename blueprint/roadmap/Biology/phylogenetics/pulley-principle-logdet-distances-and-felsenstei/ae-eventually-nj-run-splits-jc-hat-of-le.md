# Consistency of neighbor joining under Jukes–Cantor with a minimum internal edge length

Let $(G, \iota)$ be a [binary phylogenetic tree](../neighbor-joining/is-binary-phylogenetic-tree.md) on a finite set $X$ with edge lengths $w_e > 0$ and path metric $d$, let $\mu > 0$, $m > 0$ and $m \le w(ab)$ for every edge $ab$ with neither endpoint a taxon vertex. Let the sites be as in [the consistency theorem given a recovery radius](ae-eventually-nj-run-splits-jc-hat.md). Then almost surely, for all sufficiently large $n$, every run of neighbor joining on the [corrected empirical distances](jc-hat.md) of the first $n$ sites reaching at most three clusters forms exactly the splits of the internal edges of the tree (Saitou & Nei 1987; Atteson 1999).

## Sources

- N. Saitou and M. Nei, *The neighbor-joining method: a new method for reconstructing phylogenetic trees*, Mol. Biol. Evol. 4 (1987), 406–425.
- K. Atteson, *The performance of neighbor-joining methods of phylogenetic reconstruction*, Algorithmica 25 (1999), 251–278.
