# Neighbor joining is exact on tree metrics

Let $(G, \iota)$ be a [binary phylogenetic tree](is-binary-phylogenetic-tree.md) on a finite set $X$ with edge lengths $w_e > 0$, and let $d(x, y)$ be the total length of the path from $\iota(x)$ to $\iota(y)$. Let a [run of neighbor joining](njrun.md) on $d$ reach a cluster set $S$ with $|S| \le 3$, having formed the clusters $C$. Then for every set $A$ of taxa, $A \in C$ or $X \setminus A \in C$ if and only if there is an edge $ab$ with neither endpoint a taxon vertex such that $A$ is the [$a$-side](side.md) of $\{a, b\}$ (Saitou & Nei 1987; Studier & Keppler 1988; Bryant 2005).

## Sources

- N. Saitou and M. Nei, *The neighbor-joining method: a new method for reconstructing phylogenetic trees*, Mol. Biol. Evol. 4 (1987), 406–425.
- J. A. Studier and K. J. Keppler, *A note on the neighbor-joining algorithm of Saitou and Nei*, Mol. Biol. Evol. 5 (1988), 729–731.
- O. Gascuel, *A note on Sattath and Tversky's, Saitou and Nei's, and Studier and Keppler's algorithms for inferring phylogenies from evolutionary distances*, Mol. Biol. Evol. 11 (1994), 961–963.
- D. Bryant, *On the uniqueness of the selection criterion in neighbor-joining*, J. Classif. 22 (2005), 3–15.
