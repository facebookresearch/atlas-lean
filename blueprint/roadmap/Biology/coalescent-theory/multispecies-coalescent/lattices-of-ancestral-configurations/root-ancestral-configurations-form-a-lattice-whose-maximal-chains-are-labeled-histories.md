# Root ancestral configurations form a lattice whose maximal chains are labeled histories

**Setting.** Let $S$ be a rooted binary leaf-labeled species tree topology with $n$ leaves, and let a gene tree $G$ with the same labeled topology evolve inside $S$ (one gene copy per species). In a realization of $G$ in $S$, the *ancestral configuration* at a node $v$ of $S$ is the set of gene lineages present at $v$, each lineage named by its immediate descendant node of $G$. A *root ancestral configuration* is an ancestral configuration at the root of $S$; let $C(S)$ be the set of root configurations of the matching pair $(S,S)$ and $c(S) = |C(S)|$. For $a, b \in C(S)$ write $a \preceq b$ if $b$ can be obtained from $a$ by coalescing some (possibly no) lineages of $a$. A *labeled history* of $S$ is a linear ordering of its internal nodes compatible with ancestry.

**Proposition.** $(C(S), \preceq)$ is a bounded lattice. Its minimal element is the configuration of all $n$ leaf lineages, and its maximal element is the configuration consisting of the two lineages immediately descended from the root.

**Theorem.** For every labeled topology $S$ the following sets are in bijection:

1. maximal chains of the lattice $C(S)$;
2. directed paths from the minimal to the maximal element in the Hasse diagram $D(S)$ of $C(S)$;
3. labeled histories of $S$.

## Expansion

The join of $a$ and $b$ is obtained by coalescing lineages of $a$ and of $b$ until both reach a common configuration; this process ends at the configuration of the two root-adjacent lineages, so joins exist, and finiteness with a top element gives meets. A cover relation in $C(S)$ coalesces exactly one pair of sibling lineages, i.e. moves one internal node of $G$ above the species-tree root. A maximal chain from all leaves to the two root children therefore records the internal non-root nodes one at a time, each after its descendants, which is precisely a labeled history. The lattice view turns enumerations of root configurations and labeled histories into counts of elements and of maximal chains of $C(S)$.

## Sources

- Egor Lappo and Noah A. Rosenberg, "A lattice structure for ancestral configurations arising from the relationship between gene trees and species trees", *Discrete Applied Mathematics* 343 (2024), 65–81, <https://doi.org/10.1016/j.dam.2023.09.033>. Numbering as in the preprint arXiv:2111.10456v3, <https://arxiv.org/abs/2111.10456v3>: Section 2 (definitions), Proposition 1 (Section 3), Proposition 2 and Theorem 3 (Section 5).
