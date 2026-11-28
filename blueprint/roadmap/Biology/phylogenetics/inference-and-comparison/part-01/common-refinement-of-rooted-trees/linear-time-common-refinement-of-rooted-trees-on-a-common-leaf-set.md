# Linear-time common refinement of rooted trees on a common leaf set

**Setting.** A rooted phylogenetic tree $T$ on leaf set $L$ is identified with its hierarchy $\mathcal H(T)=\{L(T(v)):v\in V(T)\}$ of clusters (leaf sets below each vertex). A tree $T$ *refines* $T'$ if $\mathcal H(T')\subseteq\mathcal H(T)$; a *common refinement* of $T_1,\dots,T_k$ refines each of them. A set system is a *hierarchy* if any two members are nested or disjoint.

**Lemma (least resolved common refinement).** If $T_1,\dots,T_k$ have a common leaf set $L$ and $\mathcal H=\bigcup_{i=1}^k\mathcal H(T_i)$ is a hierarchy, there is a unique tree $T$ with $\mathcal H(T)=\mathcal H$, and it is least resolved: contracting any edge of $T$ yields a tree $T_e$ with $\mathcal H(T_e)\subsetneq\mathcal H(T)$. The trees have a common refinement iff $\mathcal H$ is a hierarchy, and then $T$ is also the output of the BUILD algorithm on the union of the triples displayed by the $T_i$.

**Theorem (LinCR).** There is an algorithm that, given $T_1,\dots,T_k$ on the same leaf set $L$, decides in $O(k|L|)$ time whether a common refinement exists and, if so, returns the tree $T$ with $\mathcal H(T)=\mathcal H(T_1)\cup\dots\cup\mathcal H(T_k)$.

## Expansion

The naive route through BUILD on all displayed triples costs at least $O(k|L|^2)$. LinCR instead identifies each inner vertex with the cluster it spans and computes, for every vertex $v$ of the union, its parent in $T$ directly: the candidates are the parents of $v$ in the input trees containing $v$ and, for trees not containing $v$, the smallest vertex of that tree above $v$. In a common refinement these candidates are pairwise comparable, and comparability reduces to comparing cluster sizes $|L(T(x))|$, so the parent is the candidate with the fewest leaves. Each tree contributes $O(|L|)$ work. A final pass checks that the reconstructed tree displays every input cluster, which certifies existence or detects incompatibility. Common refinements arise when merging gene trees or orthology-derived trees that resolve different parts of the same species history.

## Depends on

- [Hierarchy on a finite set](../../../splits-compatibility-ultrametrics-and-upgma/is-hierarchy.md)
- [Cluster system displaying a triplet](../../../splits-compatibility-ultrametrics-and-upgma/displays-triplet.md)

## Sources

- David Schaller, Marc Hellmuth, Peter F. Stadler, "A Simple Linear-Time Algorithm for the Common Refinement of Rooted Phylogenetic Trees on a Common Leaf Set", arXiv:2107.00072: Section "Theory": lemmas on the least resolved common refinement and BUILD, the parent recursion proposition, the corollary on linear time, and the main theorem on algorithm LinCR. <https://doi.org/10.48550/arXiv.2107.00072>
